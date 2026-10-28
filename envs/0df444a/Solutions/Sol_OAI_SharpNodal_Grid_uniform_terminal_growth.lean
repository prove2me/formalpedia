-- Prove2me | solution 1 for OAI.SharpNodal.Grid.uniform_terminal_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T06:18:08.458545+00:00
-- url     : https://prove2.me/submissions/4959feb4-eb8f-4bdb-a817-500f5e251d92

import Mathlib
import Definitions.Def_NodalLength
import Definitions.Def_OAIQ4Nl000
import Theorems.Thm_OAI_SharpNodal_Profiles_uniform_normalized_subdivision
import Theorems.Thm_OAI_SharpNodal_Profiles_uniform_persistence_alternative

section
-- module Solutions.OAIQ4_Nl.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Decomposition
attribute [-instance] _root_.OAI.SharpNodal.Profiles.unitDisk_volume_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
noncomputable section
open scoped Topology ContDiff
open Filter Set MeasureTheory
namespace SharpNodal.Profiles
open Carleman

lemma plane_component_norm_le (v : Plane) (i : Fin 2) : |v i|≤‖v‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridImprovement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory

namespace SharpNodal.Profiles

lemma fin_real_abs_sub_ge_one {A : ℕ} {p q : Fin A} (hne : p≠q) :
    (1:ℝ)≤|(p:ℝ)-(q:ℝ)| := by
  have hz : ((p:ℕ):ℤ)-((q:ℕ):ℤ)≠0 := by
    intro h
    have h' : (p:ℕ)=(q:ℕ) := by exact_mod_cast sub_eq_zero.mp h
    exact hne (Fin.ext h')
  exact_mod_cast Int.one_le_abs hz

lemma gridCenter_separated {A : ℕ} (hA : 0<A) {p q : GridIndex A} (hne : p≠q) :
    (A:ℝ)⁻¹≤‖gridCenter A p-gridCenter A q‖ := by
  have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr hA
  obtain ⟨i,hi⟩ : ∃i,p i≠q i := Function.ne_iff.mp hne
  have ha := fin_real_abs_sub_ge_one hi
  have hn := plane_component_norm_le (gridCenter A p-gridCenter A q) i
  have he : (gridCenter A p-gridCenter A q) i=((p i:ℝ)-(q i:ℝ))/(A:ℝ) := by
    change (((p i:ℝ)+1/2)/(A:ℝ)-1/2)-(((q i:ℝ)+1/2)/(A:ℝ)-1/2)=_
    ring
  rw [he,abs_div,abs_of_pos hAr] at hn
  have hdiv : (A:ℝ)⁻¹≤|(p i:ℝ)-(q i:ℝ)|/(A:ℝ) := by
    simpa only [one_div] using div_le_div_of_nonneg_right ha hAr.le
  exact hdiv.trans hn

lemma gridCenter_injective {A : ℕ} (hA : 0<A) : Function.Injective (gridCenter A) := by
  intro p q he
  by_contra hne
  have hh := gridCenter_separated hA hne
  rw [he,sub_self,norm_zero] at hh
  exact (not_le_of_gt (inv_pos.mpr (Nat.cast_pos.mpr hA))) hh

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma logRate_real {S : ℝ} {m : ℝ≥0∞} (hm0 : m≠0) (hmt : m≠⊤) :
    logRate S m=((Real.log m.toReal/(2*S):ℝ):EReal) := by
  rw [logRate,ENNReal.log_pos_real hm0 hmt,← EReal.coe_mul]
  congr 1
  ring

lemma tiltedMass_mono_set (S : ℝ) (B : Plane) (U : Plane → ℝ) (c : ℝ) (f : Plane → ℝ)
    {E F : Set Plane} (hEF : E⊆F) : tiltedMass S B U c f E≤tiltedMass S B U c f F := by
  exact lintegral_mono_set hEF

end SharpNodal.Profiles

noncomputable section
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_const_mul (S : ℝ) (B : Plane) (U : Plane → ℝ) (c d : ℝ)
    (hc : 0 ≤ c) (f : Plane → ℝ) (E : Set Plane) :
    tiltedMass S B U (c*d) f E=ENNReal.ofReal c*tiltedMass S B U d f E := by
  unfold tiltedMass
  simp_rw [mul_assoc,ENNReal.ofReal_mul hc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma massExcess_mul_left (c a b : ℝ≥0∞) (hc0 : c≠0) (hct : c≠⊤) :
    massExcess (c*a) (c*b)=massExcess a b := by
  unfold massExcess
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,mul_div_mul_left]
  exact ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩

lemma tiltedMass_normalized {S : ℝ} {B : Plane} {U : Plane → ℝ} {Ω : Set Plane}
    (hm0 : tiltedMass S B U 1 0 Ω≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤) :
    let c := (tiltedMass S B U 1 0 Ω).toReal⁻¹
    0 < c ∧ tiltedMass S B U c 0 Ω=1 := by
  dsimp only
  have hm : 0<(tiltedMass S B U 1 0 Ω).toReal := ENNReal.toReal_pos hm0 hmt
  refine ⟨inv_pos.mpr hm,?_⟩
  rw [← mul_one (tiltedMass S B U 1 0 Ω).toReal⁻¹,
    tiltedMass_const_mul _ _ _ _ 1 (inv_pos.mpr hm).le,ENNReal.ofReal_inv_of_pos hm,
    ENNReal.ofReal_toReal hmt,ENNReal.inv_mul_cancel hm0 hmt]

lemma normalized_inner_rate {S : ℝ} (hS : 0<S) {B : Plane} {U : Plane → ℝ}
    {Ω G : Set Plane} (hGΩ : G⊆Ω)
    (hm0 : tiltedMass S B U 1 0 G≠0) (hmt : tiltedMass S B U 1 0 Ω≠⊤)
    (hE : massExcess (tiltedMass S B U 1 0 Ω) (tiltedMass S B U 1 0 G)≤S) :
    (-1:EReal)≤logRate S (tiltedMass S B U (tiltedMass S B U 1 0 Ω).toReal⁻¹ 0 G) := by
  let a := tiltedMass S B U 1 0 Ω
  let b := tiltedMass S B U 1 0 G
  have hba : b≤a := tiltedMass_mono_set _ _ _ _ _ hGΩ
  have ha0 : a≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hba)
  have hbt : b≠⊤ := ne_top_of_le_ne_top hmt hba
  have ha : 0<a.toReal := ENNReal.toReal_pos ha0 hmt
  have hb : 0<b.toReal := ENNReal.toReal_pos hm0 hbt
  have heq : tiltedMass S B U a.toReal⁻¹ 0 G=ENNReal.ofReal a.toReal⁻¹*b := by
    simpa using tiltedMass_const_mul S B U a.toReal⁻¹ 1 (inv_pos.mpr ha).le 0 G
  have hc0 : ENNReal.ofReal a.toReal⁻¹*b≠0 := mul_ne_zero
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ha)) hm0
  have hct : ENNReal.ofReal a.toReal⁻¹*b≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt
  rw [heq,logRate_real hc0 hct,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr ha).le]
  apply EReal.coe_le_coe_iff.mpr
  have hlog : Real.log (a.toReal⁻¹*b.toReal)= -Real.log (a.toReal/b.toReal) := by
    rw [Real.log_mul (inv_ne_zero (ne_of_gt ha)) (ne_of_gt hb),Real.log_inv,
      Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
    ring
  rw [hlog]
  change Real.log (a.toReal/b.toReal)/2≤S at hE
  rw [le_div_iff₀ (by positivity : (0:ℝ)<2*S)]
  linarith

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_mono (T : Plane) (U : Plane → ℝ) (y : Plane) {r R : ℝ}
    (hrR : r≤R) : centeredMass T U y r ≤ centeredMass T U y R :=
  lintegral_mono_set (Metric.ball_subset_ball hrR)

lemma tiltedMass_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0≤d) (y : Plane) (r : ℝ) :
    tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)=
      ENNReal.ofReal (d*Real.exp (-2*inner ℝ B y))*centeredMass (B+S • c) U y r := by
  unfold tiltedMass centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  rw [← ENNReal.ofReal_mul (mul_nonneg hd (Real.exp_pos _).le)]
  congr 1
  have hw : tiltedWeight B S (fun x =>-(-inner ℝ c (x-y))) x=
      -inner ℝ B y-inner ℝ (B+S • c) (x-y) := by
    simp only [tiltedWeight,neg_neg,inner_add_left,real_inner_smul_left,inner_sub_right]
    ring
  rw [hw,sub_eq_add_neg,Real.exp_add]
  simp only [mul_pow]
  rw [← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(-inner ℝ B y)= -2*inner ℝ B y by ring]
  ring

lemma tilted_excess_centered (S : ℝ) (B c : Plane) (U : Plane → ℝ) (d : ℝ)
    (hd : 0<d) (y : Plane) (R r : ℝ) :
    massExcess (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R))
      (tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r))=
    massExcess (centeredMass (B+S • c) U y R) (centeredMass (B+S • c) U y r) := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le,tiltedMass_centered _ _ _ _ _ hd.le]
  apply massExcess_mul_left
  · exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))
  · exact ENNReal.ofReal_ne_top

lemma tilted_finite_centered {S : ℝ} {B c : Plane} {U : Plane → ℝ} {d : ℝ}
    (hd : 0<d) {y : Plane} {R r : ℝ}
    (hinner : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y r)≠0)
    (houter : tiltedMass S B U d (fun x =>-inner ℝ c (x-y)) (Metric.ball y R)≠⊤) :
    centeredMass (B+S • c) U y r≠0 ∧ centeredMass (B+S • c) U y R≠⊤ := by
  rw [tiltedMass_centered _ _ _ _ _ hd.le] at hinner houter
  refine ⟨fun h =>hinner (by simp [h]),?_⟩
  intro h
  apply houter
  rw [h,ENNReal.mul_top]
  exact ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hd (Real.exp_pos _))

lemma centeredMass_weight_bound (T T' : Plane) (U : Plane → ℝ) (y : Plane) {r : ℝ}
    : centeredMass T U y r≤
      ENNReal.ofReal (Real.exp (2*‖T-T'‖*r))*centeredMass T' U y r := by
  unfold centeredMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_pow,mul_pow,← Real.exp_nat_mul,← Real.exp_nat_mul]
  simp only [Nat.cast_ofNat]
  rw [← mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hnorm : ‖x-y‖ ≤ r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hx).le
  have hi : -inner ℝ (T-T') (x-y)≤‖T-T'‖*r :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))
  rw [inner_sub_left] at hi
  linarith

lemma massExcess_log_sub {a b : ℝ≥0∞} (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤) :
    massExcess a b=(Real.log a.toReal-Real.log b.toReal)/2 := by
  unfold massExcess
  rw [Real.log_div (ENNReal.toReal_ne_zero.mpr ⟨ha0,hat⟩) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩)]

lemma massExcess_weight_bound {a b c d : ℝ≥0∞} {α β : ℝ}
    (ha0 : a≠0) (hat : a≠⊤) (hb0 : b≠0) (hbt : b≠⊤)
    (hc0 : c≠0) (hct : c≠⊤) (hd0 : d≠0) (hdt : d≠⊤)
    (hac : a≤ENNReal.ofReal (Real.exp (2*α))*c)
    (hdb : d≤ENNReal.ofReal (Real.exp (2*β))*b) :
    massExcess a b≤ massExcess c d+α+β := by
  have haa := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct) hac)
  have hdd := (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbt) hdb)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le] at haa hdd
  have hal := Real.log_le_log (ENNReal.toReal_pos ha0 hat) haa
  have hdl := Real.log_le_log (ENNReal.toReal_pos hd0 hdt) hdd
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hc0,hct⟩),Real.log_exp] at hal
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ENNReal.toReal_ne_zero.mpr ⟨hb0,hbt⟩),Real.log_exp] at hdl
  rw [massExcess_log_sub ha0 hat hb0 hbt,massExcess_log_sub hc0 hct hd0 hdt]
  linarith

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory

noncomputable section
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma centeredMass_ne_zero_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠0) : centeredMass T' U y r≠0 := by
  intro hz
  have hh := centeredMass_weight_bound T T' U y (r:=r)
  rw [hz,mul_zero] at hh
  exact h (le_antisymm hh bot_le)

lemma centeredMass_ne_top_of {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : centeredMass T U y r≠⊤) : centeredMass T' U y r≠⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
    (centeredMass_weight_bound T' T U y)

lemma centered_excess_nonneg {T : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    0 ≤ massExcess (centeredMass T U y R) (centeredMass T U y r) := by
  have hmono := centeredMass_mono T U y hrR
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrpos := ENNReal.toReal_pos hm0 hrt
  have hm := ENNReal.toReal_mono hmt hmono
  unfold massExcess
  apply div_nonneg _ (by norm_num)
  apply Real.log_nonneg
  exact (le_div_iff₀ hrpos).mpr (by simpa using hm)

lemma centered_excess_weight_bound {T T' : Plane} {U : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hrR : r ≤ R) (hm0 : centeredMass T U y r≠0) (hmt : centeredMass T U y R≠⊤) :
    massExcess (centeredMass T U y R) (centeredMass T U y r) ≤
      massExcess (centeredMass T' U y R) (centeredMass T' U y r)+(R+r)*‖T-T'‖ := by
  have hmono := centeredMass_mono T U y hrR
  have hmono' := centeredMass_mono T' U y hrR
  have hm0' : centeredMass T' U y r≠0 := centeredMass_ne_zero_of hm0
  have hmt' : centeredMass T' U y R≠⊤ := centeredMass_ne_top_of hmt
  have hR0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hmono)
  have hR0' := ne_of_gt ((pos_iff_ne_zero.mpr hm0').trans_le hmono')
  have hrt := ne_top_of_le_ne_top hmt hmono
  have hrt' := ne_top_of_le_ne_top hmt' hmono'
  have hh := massExcess_weight_bound (α:=‖T-T'‖*R) (β:=‖T-T'‖*r)
    hR0 hmt hm0 hrt hR0' hmt' hm0' hrt'
    (by simpa only [mul_assoc] using centeredMass_weight_bound T T' U y (r:=R))
    (by simpa only [norm_sub_rev,mul_assoc] using centeredMass_weight_bound T' T U y (r:=r))
  nlinarith only [hh]

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma tiltedMass_zero_center (S : ℝ) (B : Plane) (U : Plane → ℝ) (d r : ℝ)
    (hd : 0≤d) :
    tiltedMass S B U d 0 (Metric.ball 0 r)=ENNReal.ofReal d*centeredMass B U 0 r := by
  change tiltedMass S B U d (fun _ => 0) (Metric.ball 0 r)=_
  simpa using tiltedMass_centered S B 0 U d hd 0 r

theorem one_subdivision : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ : ℝ,0<C₀ ∧
    ∀(p U : Plane → ℝ) (b : Plane) (K S s : ℝ),
    ContDiffOn ℝ ∞ p (Metric.ball 0 1000) →
    ContDiffOn ℝ ∞ U (Metric.ball 0 1000) →
    0 < K → 0 ≤ s → C₀ ≤ S →
    (∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp) →
    (∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp*s) →
    (∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0) →
    centeredMass (K • b) U 0 1≠0 → centeredMass (K • b) U 0 1000≠⊤ →
    massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)≤S →
    K/(S+‖K • b‖)≤C₀⁻¹ → K^2*s/(S*(S+‖K • b‖))≤C₀⁻¹ →
    ∃b' : Plane → Plane,
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)≤C₁*S/K ∧
      (∀y∈gridCenters A,centeredMass (K • b' y) U y ((A:ℝ)⁻¹)≠0 ∧
        centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹)≠⊤) ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))/(K*(A:ℝ)⁻¹))≤S/(2*K) := by
  obtain ⟨A,hA,Cs,hCs,hu⟩ := uniform_normalized_subdivision
  refine ⟨A,hA,Cs+1,by linarith,?_⟩
  intro Cp hCp
  obtain ⟨C₀,hC₀,hcorr⟩ := hu Cp
  refine ⟨C₀,hC₀,?_⟩
  intro p U b K S s hp hU hK _hs hSmin hpb hpd hPDE hm0 hmt hE hsmall hsmall'
  have hS : 0<S := hC₀.trans_le hSmin
  let B : Plane := K • b
  have hmass (r : ℝ) : tiltedMass S B U 1 0 (Metric.ball 0 r)=centeredMass B U 0 r := by
    simpa using tiltedMass_zero_center S B U 1 r (by norm_num)
  have hmono := centeredMass_mono B U 0 (show (1:ℝ)≤1000 by norm_num)
  have hmouter : centeredMass B U 0 1000≠0 := ne_of_gt ((pos_iff_ne_zero.mpr hm0).trans_le hmono)
  obtain ⟨hd,hnorm⟩ := tiltedMass_normalized (S:=S) (B:=B) (U:=U) (Ω:=Metric.ball 0 1000) (by simpa only [hmass] using hmouter)
    (by simpa only [hmass] using hmt)
  let D : NormalizedPDEData Cp := {
    p:=p, U:=U, B:=B, K:=K, S:=S, d:=(tiltedMass S B U 1 0 (Metric.ball 0 1000)).toReal⁻¹
    smooth_p:=hp, smooth_U:=hU, S_pos:=hS, d_pos:=hd, coefficient_bound:=hpb
    equation:=hPDE, normalized:=hnorm.le
    parent_growth:=normalized_inner_rate hS (Metric.ball_subset_ball (by norm_num))
      (by simpa only [hmass] using hm0) (by simpa only [hmass] using hmt)
      (by simpa only [hmass] using hE) }
  have hD : D.Small C₀ := by
    refine ⟨hSmin,?_,?_⟩
    · change |K/(S+‖B‖)|≤C₀⁻¹
      rw [abs_of_pos (div_pos hK (add_pos_of_pos_of_nonneg hS (norm_nonneg _)))]
      exact hsmall
    · intro i x hx
      change |K^2*coordPartial p i x/(S*(S+‖B‖))|≤Cp*C₀⁻¹
      have hden : 0<S*(S+‖B‖) := mul_pos hS (add_pos_of_pos_of_nonneg hS (norm_nonneg _))
      rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg K),abs_of_pos hden]
      calc
        _ ≤ K^2*(Cp*s)/(S*(S+‖B‖)) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpd i x hx) (sq_nonneg K)) hden.le
        _ = Cp*(K^2*s/(S*(S+‖B‖))) := by ring
        _ ≤ Cp*C₀⁻¹ := mul_le_mul_of_nonneg_left hsmall' hCp
  obtain ⟨c,hc,hfinite,havg⟩ := hcorr D hD
  let b' : Plane → Plane := fun y => b+(S/K) • c y
  have hb' (y : Plane) : K • b' y=B+S • c y := by
    simp only [b',smul_add,smul_smul,B]
    rw [mul_div_cancel₀ _ (ne_of_gt hK)]
  refine ⟨b',?_,?_,?_⟩
  · have hc' : ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)=
        (S/K)*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖)) := by
      simp only [b',add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hS hK)]
      rw [← Finset.mul_sum]
      ring
    rw [hc']
    have hh := mul_le_mul_of_nonneg_left hc (div_pos hS hK).le
    change (S/K)*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖c y‖))≤(Cs+1)*S/K
    exact hh.trans (by
      calc
        (S/K)*Cs ≤ (S/K)*(Cs+1) := mul_le_mul_of_nonneg_left (by linarith) (div_pos hS hK).le
        _ = (Cs+1)*S/K := by ring)
  · intro y hy
    rw [hb']
    exact tilted_finite_centered hd (hfinite y hy).1 (hfinite y hy).2
  · have hAr : 0<(A:ℝ) := Nat.cast_pos.mpr (by omega)
    have hρ : 0<(A:ℝ)⁻¹ := inv_pos.mpr hAr
    have hex (y : Plane) :
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))=gridExcess A S B U D.d c y := by
      rw [hb']
      exact (tilted_excess_centered S B (c y) U D.d hd y _ _).symm
    simp_rw [hex]
    have heq : ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A S B U D.d c y/(K*(A:ℝ)⁻¹))=
        (S/(K*(A:ℝ)⁻¹))*(((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,gridExcess A S B U D.d c y/S)) := by
      rw [← Finset.sum_div,← Finset.sum_div]
      field_simp
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left havg.le (div_pos hS (mul_pos hK hρ)).le
    convert hh using 1 <;> first | rfl | field_simp

end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Descent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma UnitWave.excess_nonneg {Cp a₀ : ℝ} (D : UnitWave Cp a₀) (b : Plane) :
    0≤D.excess b :=
  centered_excess_nonneg (by norm_num) (centeredMass_ne_zero_of D.inner_nonzero)
    (centeredMass_ne_top_of D.outer_finite)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma descent_smallness {C K s E E₀ t : ℝ} (hC : 0<C) (hK : 0<K) (hs : 0 ≤ s)
    (hE : 0≤E) (ht : 0≤t) (hcomp : E₀ ≤ E+1001*K*t)
    (hlarge : 2*(C+1)*1001<E₀/K ∨ 2*(C+1)*1001<t) :
    let S:=E+(C+1)+K*s
    C≤S ∧ E≤S ∧ K/(S+K*t)≤C⁻¹ ∧ K^2*s/(S*(S+K*t))≤C⁻¹ := by
  dsimp only
  have hS : 0<E+(C+1)+K*s := by positivity
  have hSK : K*s≤E+(C+1)+K*s := by linarith
  have hden : 0<E+(C+1)+K*s+K*t := by positivity
  have hmajor : C*K≤E+(C+1)+K*s+K*t := by
    rcases hlarge with h | h
    · have hh := (lt_div_iff₀ hK).mp h
      have hEs : E≤E+(C+1)+K*s := by nlinarith [mul_nonneg hK.le hs]
      have hE' : E≤1001*(E+(C+1)+K*s) := by nlinarith
      nlinarith [mul_pos hC hK]
    · have hh := mul_lt_mul_of_pos_left h hK
      nlinarith [mul_nonneg hK.le hs,mul_pos hC hK]
  have hrat : K/(E+(C+1)+K*s+K*t)≤C⁻¹ := by
    apply (div_le_iff₀ hden).mpr
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hC).mpr (by nlinarith only [hmajor])
  refine ⟨by nlinarith [mul_nonneg hK.le hs],by nlinarith [mul_nonneg hK.le hs],hrat,?_⟩
  apply le_trans _ hrat
  apply (div_le_div_iff₀ (mul_pos hS hden) hden).mpr
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSK hK.le) hden.le
  nlinarith only [hh]

theorem one_step_descent : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ L : ℝ,1≤C₀ ∧ 0<L ∧
    ∀(p U : Plane → ℝ) (b : Plane) (K s : ℝ),
    ContDiffOn ℝ ∞ p (Metric.ball 0 1000) →
    ContDiffOn ℝ ∞ U (Metric.ball 0 1000) → 0<K → 0 ≤ s →
    (∀x∈Metric.ball (0:Plane) 1000,|p x|≤Cp) →
    (∀i x,x∈Metric.ball (0:Plane) 1000 → |coordPartial p i x|≤Cp*s) →
    (∀x∈Metric.ball (0:Plane) 1000,euclideanLaplacian U x+K^2*p x*U x=0) →
    centeredMass 0 U 0 1≠0 → centeredMass 0 U 0 1000≠⊤ →
    (L < massExcess (centeredMass 0 U 0 1000) (centeredMass 0 U 0 1)/K ∨ L<‖b‖) →
    let m:=massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)/K
    let f:=C₀/K+s
    ∃b' : Plane → Plane,
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,‖b' y-b‖)≤C₁*(m+f) ∧
      (∀y∈gridCenters A,centeredMass (K • b' y) U y ((A:ℝ)⁻¹)≠0 ∧
        centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹)≠⊤) ∧
      ((A:ℝ)⁻¹)^2*(∑y∈gridCenters A,
        massExcess (centeredMass (K • b' y) U y (1000*(A:ℝ)⁻¹))
          (centeredMass (K • b' y) U y ((A:ℝ)⁻¹))/(K*(A:ℝ)⁻¹))≤(m+f)/2 := by
  obtain ⟨A,hA,C₁,hC₁,hsub⟩ := one_subdivision
  refine ⟨A,hA,C₁,hC₁,?_⟩
  intro Cp hCp
  obtain ⟨C,hC,hsub⟩ := hsub Cp hCp
  refine ⟨C+1,2*(C+1)*1001,by linarith,by positivity,?_⟩
  intro p U b K s hp hU hK hs hpb hpd hPDE hm0 hmt hlarge
  dsimp only
  have hb0 : centeredMass (K • b) U 0 1≠0 := centeredMass_ne_zero_of hm0
  have hbt : centeredMass (K • b) U 0 1000≠⊤ := centeredMass_ne_top_of hmt
  let E:=massExcess (centeredMass (K • b) U 0 1000) (centeredMass (K • b) U 0 1)
  have hE : 0≤E := centered_excess_nonneg (by norm_num) hb0 hbt
  have hnorm : ‖K • b‖=K*‖b‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hK]
  have hc := centered_excess_weight_bound (T':=K • b) (by norm_num : (1:ℝ)≤1000) hm0 hmt
  simp only [zero_sub,norm_neg,hnorm] at hc
  obtain ⟨hmin,hEs,hrat,hrat'⟩ := descent_smallness hC hK hs hE (norm_nonneg b)
    (by dsimp [E]; nlinarith only [hc]) hlarge
  rw [← hnorm] at hrat hrat'
  obtain ⟨b',hinc,hfinite,hdec⟩ := hsub p U b K (E+(C+1)+K*s) s hp hU hK hs hmin
    hpb hpd hPDE hb0 hbt hEs hrat hrat'
  refine ⟨b',?_,hfinite,?_⟩
  · convert hinc using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [E]
    field_simp
    ring
  · convert hdec using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [E]
    field_simp
    ring

end SharpNodal.Profiles

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_StoppedTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory

namespace SharpNodal.Descent

namespace Tree
variable {ι : Type*} [Fintype ι]

theorem stopped_descent {C : ℝ} (hC : 0 ≤ C) {t : Tree ι} (h : Valid C t) :
    t.massCost ≤ 2*t.root.mass+t.floorCost ∧
    t.tiltCost ≤ 2*C*t.root.mass+2*C*t.floorCost := by
  induction t with
  | stop a =>
    dsimp [massCost,tiltCost,floorCost,root]
    constructor
    · linarith [h.1]
    · have hm := h.1
      positivity
  | step a t ih =>
    have hm := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).1)
    have ht := Finset.expect_le_expect (fun i (_ : i∈(Finset.univ : Finset ι)) =>
      (ih i (h.2.2.2.2 i)).2)
    simp only [Finset.expect_add_distrib,← Finset.mul_expect] at hm ht
    have hs := h.2.2.1
    have hi := h.2.2.2.1
    change a.mass + (𝔼 i, massCost (t i)) ≤ 2*a.mass+(a.floor+(𝔼 i, floorCost (t i))) ∧
      (𝔼 i, (‖(root (t i)).tilt-a.tilt‖+tiltCost (t i))) ≤
        2*C*a.mass+2*C*(a.floor+(𝔼 i, floorCost (t i)))
    rw [Finset.expect_add_distrib]
    constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ)≤2) hC)]

end Tree
end SharpNodal.Descent

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_ScaledWaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace

namespace SharpNodal.Profiles
open Carleman

lemma centered_excess_rescale (T : Plane) (U : Plane → ℝ) (y z : Plane) {s : ℝ}
    (hs : 0 < s) (R r : ℝ) :
    massExcess (centeredMass (s • T) (U ∘ rescaleMap y s) z R)
      (centeredMass (s • T) (U ∘ rescaleMap y s) z r)=
      massExcess (centeredMass T U (rescaleMap y s z) (s*R))
      (centeredMass T U (rescaleMap y s z) (s*r)) := by
  rw [centeredMass_rescale _ _ _ _ hs,centeredMass_rescale _ _ _ _ hs]
  exact massExcess_mul_left _ _ _ (by simp [hs.ne'])
    (by simp)

end SharpNodal.Profiles
noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma grid_expect {A : ℕ} (hA : 0<A) (f : Plane → ℝ) :
    (𝔼 i : GridIndex A, f (gridCenter A i))=((A:ℝ)⁻¹)^2*∑y∈gridCenters A,f y := by
  classical
  rw [Fintype.expect_eq_sum_div_card,gridCenters,
    Finset.sum_image (fun i _ j _ h =>gridCenter_injective hA h)]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  ring

end SharpNodal.Profiles

noncomputable section
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
namespace SharpNodal.Profiles
open Carleman

lemma ScaledWave.child_growth {Cp a₀ : ℝ} (D : ScaledWave Cp a₀) {A : ℕ} (hA : 2≤A)
    (i : GridIndex A) (hbottom : a₀≤D.K/(A:ℝ))
    (hm0 : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0)
    (hmt : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤) (b : Plane) :
    (D.child hA i hbottom hm0 hmt).growth b=
      massExcess (centeredMass (D.K • b) D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b) D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) := by
  have hAr : 0<(A:ℝ) := by exact_mod_cast (show 0<A by omega)
  have he:= centered_excess_rescale (D.K • b) D.U (gridCenter A i) 0 (inv_pos.mpr hAr) 1000 1
  have hs : (A:ℝ)⁻¹ • (D.K • b)=(D.K/(A:ℝ)) • b := by rw [smul_smul]; congr 1; ring
  simp only [hs,rescaleMap,smul_zero,add_zero,mul_one] at he
  dsimp only [UnitWave.growth,UnitWave.excess,ScaledWave.child]
  rw [he]
  simp only [div_eq_mul_inv,mul_comm]

theorem actual_descent_rule : ∃A : ℕ,10000<A ∧ ∃C₁ : ℝ,0<C₁ ∧
    ∀Cp : ℝ,0≤Cp → ∃C₀ L : ℝ,1≤C₀ ∧ 0<L ∧
    ∀a₀ : ℝ,0<a₀ → DescentRule A Cp a₀ C₀ C₁ L := by
  obtain ⟨A,hA,C₁,hC₁,hstep⟩ := one_step_descent
  refine ⟨A,hA,C₁,hC₁,?_⟩
  intro Cp hCp
  obtain ⟨C₀,L,hC₀,hL,hstep⟩ := hstep Cp hCp
  refine ⟨C₀,L,hC₀,hL,?_⟩
  intro a₀ ha₀ D b hbottom hlarge
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  obtain ⟨b',hinc,hfinite,hdec⟩ := hstep D.p D.U b D.K D.side D.smooth_p D.smooth_U hK
    D.side_pos.le D.coefficient_bound D.physical_derivative D.equation D.inner_nonzero D.outer_finite
    (by simpa only [UnitWave.growth,UnitWave.excess,smul_zero] using hlarge)
  have hmem (i : GridIndex A) : gridCenter A i∈gridCenters A := Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
  have hm0 (i : GridIndex A) : centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹≠0 :=
    centeredMass_ne_zero_of (hfinite _ (hmem i)).1
  have hmt (i : GridIndex A) : centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹)≠⊤ :=
    centeredMass_ne_top_of (hfinite _ (hmem i)).2
  let E (i : GridIndex A) := D.child (by omega : 2≤A) i hbottom (hm0 i) (hmt i)
  refine ⟨E,(fun i =>b' (gridCenter A i)),fun i =>⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · rw [grid_expect (by omega : 0<A) (fun y =>‖b' y-b‖)]
    exact hinc
  · have hg (i : GridIndex A) := D.child_growth (by omega : 2≤A) i hbottom (hm0 i) (hmt i) (b' (gridCenter A i))
    simp_rw [show ∀i,(E i).growth (b' (gridCenter A i))=
      massExcess (centeredMass (D.K • b' (gridCenter A i)) D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b' (gridCenter A i)) D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) from hg]
    rw [grid_expect (by omega : 0<A) (fun y =>
      massExcess (centeredMass (D.K • b' y) D.U y (1000*(A:ℝ)⁻¹))
        (centeredMass (D.K • b' y) D.U y (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹))]
    exact hdec

end SharpNodal.Profiles
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace SharpNodal.Descent.Tree
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scaled_floor_bound {A C₀ : ℝ} (hA : 2≤A) (hC : 0≤C₀) (n : ℕ)
    {K s : ℝ} (hK : 0 < K) (hs : 0 ≤ s) (t : Tree ι) (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤(2*A^n-1)*C₀/K+2*s := by
  have hApos : 0<A := by linarith
  have hAp : 1≤A^n := one_le_pow₀ (by linarith : (1:ℝ)≤A)
  induction n generalizing K s t with
  | zero =>
    cases t with
    | stop a => simp only [floorCost,pow_zero]; positivity
    | step a t => exact ht.elim
  | succ n ih =>
    cases t with
    | stop a =>
      change 0≤_
      have hh : 0≤2*A^(n+1)-1 := by linarith
      positivity
    | step a t =>
      have hb (i : ι) := ih (div_pos hK hApos) (div_nonneg hs hApos.le) (t i) (ht.2 i) (one_le_pow₀ (by linarith : (1:ℝ)≤A))
      have he := Finset.expect_le Finset.univ_nonempty (fun i _ => hb i)
      change a.floor+(𝔼 i,floorCost (t i))≤_
      rw [ht.1]
      apply le_trans (show C₀/K+s+(𝔼 i,floorCost (t i)) ≤
        C₀/K+s+((2*A^n-1)*C₀/(K/A)+2*(s/A)) from by linarith only [he])
      have hCs : 0≤C₀/K := div_nonneg hC hK.le
      have hsA : s / A ≤ s / 2 := div_le_div_of_nonneg_left hs (by norm_num) hA
      have hCA : C₀/K*2≤C₀/K*A := mul_le_mul_of_nonneg_left hA hCs
      have heq : (2*A^n-1)*C₀/(K/A)=(2*A^(n+1)-A)*(C₀/K) := by
        rw [pow_succ]
        field_simp
      rw [heq]
      change C₀/K+s+((2*A^(n+1)-A)*(C₀/K)+2*(s/A))≤(2*A^(n+1)-1)*C₀/K+2*s
      rw [mul_div_assoc]
      nlinarith only [hsA,hCA]

lemma physical_floor_bound {A C₀ a₀ K s : ℝ} (hA : 2≤A) (hC : 0≤C₀) (ha : 0<a₀)
    (hK : 0 < K) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ)
    (hbottom : a₀≤K/A^n) {t : Tree ι} (ht : ScaledFloors A C₀ K s n t) :
    t.floorCost≤2*(C₀/a₀+1) := by
  have hAp : 0<A^n := pow_pos (by linarith : (0:ℝ)<A) n
  have hkbottom := (le_div_iff₀ hAp).mp hbottom
  have hratio : C₀*A^n/K≤C₀/a₀ := by
    apply (div_le_div_iff₀ hK ha).mpr
    nlinarith [mul_le_mul_of_nonneg_left hkbottom hC]
  have hb := scaled_floor_bound hA hC n hK hs t ht
  have hCK : 0≤C₀/K := div_nonneg hC hK.le
  have he : (2*A^n-1)*C₀/K=2*(C₀*A^n/K)-C₀/K := by ring
  rw [he] at hb
  linarith

end SharpNodal.Descent.Tree

noncomputable section
open scoped BigOperators
open Set MeasureTheory
namespace SharpNodal.Profiles

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

lemma numerical_root (C₀ : ℝ) (t : WaveTree A Cp a₀) :
    (t.numerical C₀).root=label C₀ t.rootWave t.rootTilt := by cases t <;> rfl

lemma coherent_floors (C₀ : ℝ) {n : ℕ} {t : WaveTree A Cp a₀} (ht : Coherent n t) :
    Descent.Tree.ScaledFloors (A:ℝ) C₀ t.rootWave.K t.rootWave.side n (t.numerical C₀) := by
  induction n generalizing t with
  | zero => cases t with
    | stop D b => trivial
    | step D b t => exact ht.elim
  | succ n ih => cases t with
    | stop D b => trivial
    | step D b t =>
      refine ⟨rfl,fun i =>?_⟩
      have hh := ih (ht i).2
      rw [(ht i).1.2.2.1,(ht i).1.2.2.2] at hh
      exact hh

lemma label_nonnegative (ha₀ : 0<a₀) {C₀ : ℝ} (hC₀ : 0≤C₀)
    (D : ScaledWave Cp a₀) (b : Plane) :
    0≤(label C₀ D b).mass ∧ 0≤(label C₀ D b).floor := by
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  exact ⟨div_nonneg (D.excess_nonneg b) hK.le,add_nonneg (div_nonneg hC₀ hK.le) D.side_pos.le⟩

end WaveTree
end SharpNodal.Profiles

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_GridPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory

namespace SharpNodal.Profiles

lemma wordIndex_injective (A n : ℕ) : Function.Injective (wordIndex A n) := by
  induction n with
  | zero => intro p q _; exact Subsingleton.elim _ _
  | succ n ih =>
    intro p q hpq
    have hpairs (j : Fin 2) :
        (p 0 j,wordIndex A n (Fin.tail p) j)=(q 0 j,wordIndex A n (Fin.tail q) j) := by
      apply finProdFinEquiv.injective
      exact Fin.cast_injective (pow_succ' A n).symm (congrFun hpq j)
    have hhead : p 0=q 0 := funext (fun j =>congrArg Prod.fst (hpairs j))
    have htail : Fin.tail p=Fin.tail q := ih (funext (fun j =>congrArg Prod.snd (hpairs j)))
    rw [← Fin.cons_self_tail p,← Fin.cons_self_tail q,hhead,htail]

lemma gridWord_card (A n : ℕ) : Fintype.card (GridWord A n)=(A^n)^2 := by
  simp only [GridWord,GridIndex,Fintype.card_fun,Fintype.card_fin]
  rw [← pow_mul,← pow_mul,Nat.mul_comm]

lemma expect_word_succ {α : Type*} [Fintype α] (n : ℕ) (f : (Fin (n+1) → α) → ℝ) :
    (𝔼 w,f w)=𝔼 a,𝔼 v : Fin n → α,f (Fin.cons a v) := by
  have he := Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n+1) => α))
    (fun p : α × (Fin n → α) => f (Fin.cons p.1 p.2)) f (fun _ =>rfl)
  rw [← he]
  exact Finset.expect_product _ _ _

end SharpNodal.Profiles

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Lattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set

namespace SharpNodal.Grid

lemma card_box (a b : Point) : (box a b).card=∏i : Fin 2,(b i-a i).toNat := by
  simp [box]

lemma box_mono {a b c d : Point} (ha : ∀i,c i≤a i) (hb : ∀i,b i≤d i) :
    box a b⊆box c d := by
  intro z hz
  rw [mem_box] at hz ⊢
  exact fun i =>⟨(ha i).trans (hz i).1,(hz i).2.trans_le (hb i)⟩

@[simp] lemma card_square (s : ℕ) (p : Point) : (square s p).card=s^2 := by
  rw [square,card_box]
  have hh (i : Fin 2) : ((p i+1)*(s:ℤ)-p i*s).toNat=s := by
    rw [add_mul,one_mul,add_sub_cancel_left,Int.toNat_natCast]
  simp only [hh,Fin.prod_univ_two]
  ring

lemma mem_square_div {s : ℕ} (hs : 0 < s) {p z : Point} :
    z∈square s p ↔ ∀i,z i/(s:ℤ)=p i := by
  rw [mem_square]
  have hs' : (0:ℤ) < s := by exact_mod_cast hs
  apply forall_congr'
  intro i
  rw [←Int.le_ediv_iff_mul_le hs',←Int.ediv_lt_iff_lt_mul hs']
  omega

@[simp] lemma card_neighborhood (D s : ℕ) (p : Point) :
    (neighborhood D s p).card=((2*D+1)*s)^2 := by
  rw [neighborhood,card_box]
  have hh (i : Fin 2) : ((p i+1+D)*(s:ℤ)-(p i-D)*s).toNat=(2*D+1)*s := by
    have he : (p i+1+D)*(s:ℤ)-(p i-D)*s=(((2*D+1)*s:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  simp only [hh,Fin.prod_univ_two]
  ring

lemma square_subset_neighborhood (D s : ℕ) (p : Point) : square s p⊆neighborhood D s p := by
  apply box_mono <;> intro i <;> nlinarith [Int.natCast_nonneg D,Int.natCast_nonneg s]

end SharpNodal.Grid

noncomputable section
open scoped BigOperators Topology
open Set MeasureTheory
namespace SharpNodal.Profiles

lemma UnitWave.growth_nonneg {Cp a₀ : ℝ} (ha₀ : 0<a₀) (D : UnitWave Cp a₀) (b : Plane) :
    0≤D.growth b := div_nonneg (D.excess_nonneg b) (ha₀.le.trans D.frequency_lower)

lemma UnitWave.growth_change {Cp a₀ : ℝ} (ha₀ : 0<a₀) (D : UnitWave Cp a₀) (b c : Plane) :
    D.growth b≤D.growth c+1001*‖b-c‖ := by
  have hK : 0<D.K := ha₀.trans_le D.frequency_lower
  have hh := centered_excess_weight_bound (T:=D.K • b) (T':=D.K • c)
    (by norm_num : (1:ℝ)≤1000) (centeredMass_ne_zero_of D.inner_nonzero)
    (centeredMass_ne_top_of D.outer_finite)
  simp only [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hK] at hh
  dsimp only [UnitWave.growth,UnitWave.excess]
  rw [div_le_iff₀ hK]
  have he : (massExcess (centeredMass (D.K • c) D.U 0 1000)
      (centeredMass (D.K • c) D.U 0 1)/D.K+1001*‖b-c‖)*D.K=
      massExcess (centeredMass (D.K • c) D.U 0 1000)
      (centeredMass (D.K • c) D.U 0 1)+(1000+1)*(D.K*‖b-c‖) := by field_simp; ring
  rw [he]
  exact hh

lemma GridChild.same_growth {A : ℕ} {Cp a₀ : ℝ} {D E F : ScaledWave Cp a₀} {i : GridIndex A}
    (hE : GridChild A D E i) (hF : GridChild A D F i) (b : Plane) : E.growth b=F.growth b := by
  dsimp only [UnitWave.growth,UnitWave.excess]
  rw [hE.2.1,hF.2.1,hE.2.2.1,hF.2.2.1]

theorem entry_growth_bound {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (D : ScaledWave Cp a₀)
    {H : ℝ} (hparent : D.growth 0≤H) (hbottom : a₀≤D.K/(A:ℝ))
    (i : GridIndex A) (Q : ScaledWave Cp a₀) (hQ : GridChild A D Q i) :
    Q.growth 0≤(A:ℝ)^2*((1/2+1001*C₁)*(H+1001*(L+1)+C₀/a₀+1)+1001*(L+1)) := by
  classical
  have : NeZero A := ⟨by omega⟩
  let b : Plane := (L+1) • EuclideanSpace.single 0 1
  have hb : ‖b‖=L+1 := by simp [b,norm_smul,abs_of_pos (by linarith : 0<L+1)]
  obtain ⟨E,b',hc,hi,hm⟩ := hrule D b hbottom (Or.inr (by rw [hb]; linarith))
  let f := C₀/D.K+D.side
  let S := H+1001*(L+1)+C₀/a₀+1
  have hf : f≤C₀/a₀+1 := add_le_add (div_le_div_of_nonneg_left hC₀ ha₀ D.frequency_lower) D.side_le_one
  have hs : D.growth b+f≤S := by
    have hh := D.toUnitWave.growth_change ha₀ b 0
    simp only [sub_zero,hb] at hh
    dsimp [S]
    linarith
  have hn (j : GridIndex A) : ‖b' j‖≤‖b' j-b‖+‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (b' j-b) b
  have hg (j : GridIndex A) : (E j).growth 0≤(E j).growth (b' j)+1001*(‖b' j-b‖+‖b‖) := by
    have hh := (E j).toUnitWave.growth_change ha₀ 0 (b' j)
    simp only [zero_sub,norm_neg] at hh
    linarith [hn j]
  have havg := Finset.expect_le_expect (s:=Finset.univ) (fun j _ =>hg j)
  simp only [Finset.expect_add_distrib,←Finset.mul_expect,Fintype.expect_const,hb] at havg
  have havg' : (𝔼 j,(E j).growth 0)≤(1/2+1001*C₁)*S+1001*(L+1) := by
    have hprod := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤1/2+1001*C₁)
    change (𝔼 j,(E j).growth (b' j))≤(D.growth b+f)/2 at hm
    change (𝔼 j,‖b' j-b‖)≤C₁*(D.growth b+f) at hi
    nlinarith only [havg,hm,hi,hprod]
  have hsingle : (E i).growth 0≤∑j : GridIndex A,(E j).growth 0 :=
    Finset.single_le_sum (fun j _ =>(E j).toUnitWave.growth_nonneg ha₀ 0) (Finset.mem_univ i)
  have hAr : 0<(A:ℝ) := by exact_mod_cast (show 0<A by omega)
  rw [Fintype.expect_eq_sum_div_card] at havg'
  have hh := (div_le_iff₀ (by positivity : (0:ℝ)<(Fintype.card (GridIndex A):ℝ))).mp havg'
  have hh' : (∑j : GridIndex A,(E j).growth 0)≤(A:ℝ)^2*
      ((1/2+1001*C₁)*(H+1001*(L+1)+C₀/a₀+1)+1001*(L+1)) := by
    simpa only [GridIndex,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,S,mul_comm] using hh
  rw [hQ.same_growth (hc i) 0]
  exact hsingle.trans hh'

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
open Set
namespace SharpNodal.Grid

theorem finite_witness_packing {Q X : Type*} [DecidableEq Q] [DecidableEq X]
    (S : Finset Q) (U : Finset X) (Y : Q → Finset X)
    (rank : Q → ℕ) (total : X → ℕ) (d : Q → X → ℕ) (W c B J : ℕ)
    (hlower : W ≤ c*∑q∈S,(Y q).card)
    (herror : (∑q∈S,∑x∈Y q,d q x)≤B*W)
    (hambient : ∀q∈S,Y q⊆U)
    (hdisjoint : ∀q∈S,∀q'∈S,rank q=rank q' → q≠q' → Disjoint (Y q) (Y q'))
    (hrank : ∀q∈S,∀x∈Y q,rank q≤total x+d q x+J+1 ∧ total x ≤ rank q+d q x+J+1) :
    W≤2*c*(2*(2*c*B+J+1)+1)*U.card := by
  classical
  let M:=2*c*B
  let K:=M+J+1
  let Z : Q → Finset X := fun q =>(Y q).filter (fun x =>d q x≤M)
  let Bad : Q → Finset X := fun q =>(Y q).filter (fun x =>¬d q x≤M)
  have hsplit (q : Q) : (Z q).card+(Bad q).card=(Y q).card :=
    Finset.card_filter_add_card_filter_not _
  have hmark (q : Q) : (M+1)*(Bad q).card≤∑x∈Y q,d q x := by
    calc
      (M+1)*(Bad q).card=∑x∈Bad q,(M+1) := by simp [mul_comm]
      _≤∑x∈Bad q,d q x := Finset.sum_le_sum (fun x hx =>by
        have hh:¬d q x≤M := (Finset.mem_filter.mp hx).2
        omega)
      _≤∑x∈Y q,d q x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
  have hmarksum : (M+1)*(∑q∈S,(Bad q).card)≤B*W := by
    calc
      _=∑q∈S,(M+1)*(Bad q).card := Finset.mul_sum _ _ _
      _≤∑q∈S,∑x∈Y q,d q x := Finset.sum_le_sum (fun q _ =>hmark q)
      _≤_ := herror
  have hsumeq : (∑q∈S,(Z q).card)+(∑q∈S,(Bad q).card)=∑q∈S,(Y q).card := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ =>hsplit q)
  have hgood : W≤2*c*∑q∈S,(Z q).card := by
    dsimp only [M] at hmarksum
    have hb : 2*c*(∑q∈S,(Bad q).card)≤W := by
      by_cases hB : B=0
      · simp only [hB,mul_zero,zero_add,one_mul,zero_mul] at hmarksum
        have hz : (∑q∈S,(Bad q).card)=0 := Nat.eq_zero_of_le_zero hmarksum
        simp only [hz,mul_zero,Nat.zero_le]
      · apply Nat.le_of_mul_le_mul_right (c:=B) _ (Nat.pos_of_ne_zero hB)
        calc
          _=(2*c*B)*(∑q∈S,(Bad q).card) := by ring
          _≤(2*c*B+1)*(∑q∈S,(Bad q).card) := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
          _≤B*W := hmarksum
          _=W*B := Nat.mul_comm _ _
    rw [←hsumeq] at hlower
    have htwice := Nat.add_le_add hlower hlower
    have he : c*((∑q∈S,(Z q).card)+(∑q∈S,(Bad q).card))+
        c*((∑q∈S,(Z q).card)+(∑q∈S,(Bad q).card))=
        2*c*(∑q∈S,(Z q).card)+2*c*(∑q∈S,(Bad q).card) := by ring
    rw [he] at htwice
    exact Nat.le_of_add_le_add_right (htwice.trans (Nat.add_le_add_left hb _))
  have hcount (x : X) : (S.filter (fun q =>x∈Z q)).card≤2*K+1 := by
    have hmap : Set.MapsTo rank (S.filter (fun q =>x∈Z q)) (Finset.Icc (total x-K) (total x+K)) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hq,hx⟩
      rcases Finset.mem_filter.mp hx with ⟨hx,hd⟩
      have hh:=hrank q hq x hx
      rw [Finset.mem_coe,Finset.mem_Icc]
      dsimp only [K]
      omega
    have hinj : Set.InjOn rank (S.filter (fun q =>x∈Z q)) := by
      intro q hq q' hq' he
      by_contra hne
      rcases Finset.mem_filter.mp hq with ⟨hq,hx⟩
      rcases Finset.mem_filter.mp hq' with ⟨hq',hx'⟩
      exact Finset.disjoint_left.mp (hdisjoint q hq q' hq' he hne)
        (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx').1
    have hh:=Finset.card_le_card_of_injOn rank hmap hinj
    rw [Nat.card_Icc] at hh
    omega
  have hsumcount : (∑q∈S,(Z q).card)=(∑x∈U,(S.filter (fun q =>x∈Z q)).card) := by
    have hh:=Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=S) (t:=U)
      (fun q x =>x∈Z q)
    simp only [Finset.bipartiteBelow,Finset.bipartiteAbove] at hh
    rw [←hh]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx =>⟨hambient q hq ((Finset.mem_filter.mp hx).1),hx⟩,fun hx =>hx.2⟩
  have hupper : (∑q∈S,(Z q).card)≤(2*K+1)*U.card := by
    rw [hsumcount]
    calc
      _≤∑x∈U,(2*K+1) := Finset.sum_le_sum (fun x _ =>hcount x)
      _=_ := by simp [mul_comm]
  dsimp only [K,M] at hupper
  exact hgood.trans (by nlinarith)

end SharpNodal.Grid

end
end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Cells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set

namespace SharpNodal.Grid

@[simp] lemma Cell.card_points (A : ℕ) (Q : Cell) : (Q.points A).card=(Q.side A)^2 := card_square _ _
@[simp] lemma Cell.card_near (A D : ℕ) (Q : Cell) : (Q.near A D).card=((2*D+1)*Q.side A)^2 := card_neighborhood _ _ _

lemma Cell.side_pos {A : ℕ} (hA : 0<A) (Q : Cell) : 0<Q.side A := pow_pos hA _
lemma Cell.side_mono {A : ℕ} (hA : 1≤A) {Q F : Cell} (h : Q.level≤F.level) : Q.side A≤F.side A :=
  Nat.pow_le_pow_right hA h

lemma square_subset_iff {s t : ℕ} (hs : 0 < s) {p q : Point} :
    square s p⊆square t q ↔ ∀i,q i*t≤p i*s ∧ (p i+1)*s≤(q i+1)*t := by
  have hs' : (0:ℤ) < s := by exact_mod_cast hs
  constructor
  · intro h i
    have hlo : (fun j =>p j*s)∈square s p := mem_square.mpr (fun j =>by constructor <;> nlinarith)
    have hhi : (fun j =>(p j+1)*s-1)∈square s p := mem_square.mpr (fun j =>by constructor <;> nlinarith)
    exact ⟨(mem_square.mp (h hlo) i).1,by have hh:=(mem_square.mp (h hhi) i).2; omega⟩
  · intro h z hz
    apply mem_square.mpr
    intro i
    exact ⟨(h i).1.trans (mem_square.mp hz i).1,(mem_square.mp hz i).2.trans_le (h i).2⟩

lemma neighborhood_mono {s t D : ℕ} {p q : Point} (hst : s≤t)
    (hbox : ∀i,q i*t≤p i*s ∧ (p i+1)*s≤(q i+1)*t) :
    neighborhood D s p⊆neighborhood D t q := by
  have hst' : (s:ℤ)≤t := by exact_mod_cast hst
  have hD : (0:ℤ)≤D := Int.natCast_nonneg D
  apply box_mono <;> intro i <;> have hh:=hbox i <;> nlinarith

lemma Cell.near_mono {A D : ℕ} (hA : 0<A) {Q F : Cell}
    (hlevel : Q.level≤F.level) (hsub : Q.points A⊆F.points A) : Q.near A D⊆F.near A D := by
  exact neighborhood_mono (Q.side_mono hA hlevel)
    ((square_subset_iff (Q.side_pos hA)).mp hsub)

lemma Cell.div_of_mem {A : ℕ} (hA : 0<A) {Q : Cell} {z : Point} (hz : z∈Q.points A)
    {n : ℕ} (hn : Q.level≤n) (i : Fin 2) : z i/(A:ℤ)^n=Q.pos i/(A:ℤ)^(n-Q.level) := by
  have hh:=((mem_square_div (Q.side_pos hA)).mp hz) i
  have he : n=Q.level+(n-Q.level) := by omega
  rw [he,pow_add,←Int.ediv_ediv_of_nonneg (by positivity : (0:ℤ)≤(A:ℤ)^Q.level)]
  simpa only [Nat.add_sub_cancel_left,Cell.side,Nat.cast_pow] using congrArg (fun x : ℤ =>x/(A:ℤ)^(n-Q.level)) hh

lemma Cell.subset_of_intersection {A : ℕ} (hA : 0<A) {Q F : Cell}
    (hlevel : Q.level≤F.level) {z : Point} (hzQ : z∈Q.points A) (hzF : z∈F.points A) :
    Q.points A⊆F.points A := by
  intro y hy
  apply (mem_square_div (F.side_pos hA)).mpr
  intro i
  have hy':=Q.div_of_mem hA hy hlevel i
  have hz':=Q.div_of_mem hA hzQ hlevel i
  have hf:=((mem_square_div (F.side_pos hA)).mp hzF) i
  simpa only [Cell.side,Nat.cast_pow] using hy'.trans (hz'.symm.trans hf)

lemma Cell.subset_or_disjoint {A : ℕ} (hA : 0<A) {Q F : Cell}
    (hlevel : Q.level≤F.level) : Q.points A⊆F.points A ∨ Disjoint (Q.points A) (F.points A) := by
  by_cases hh : Disjoint (Q.points A) (F.points A)
  · exact Or.inr hh
  · obtain ⟨z,hzQ,hzF⟩:=Finset.not_disjoint_iff.mp hh
    exact Or.inl (Cell.subset_of_intersection hA hlevel hzQ hzF)

lemma Cell.equal_level_eq_of_intersection {A : ℕ} (hA : 0<A) {Q F : Cell}
    (hlevel : Q.level=F.level) {z : Point} (hzQ : z∈Q.points A) (hzF : z∈F.points A) : Q=F := by
  have hp : Q.pos=F.pos := by
    funext i
    have hq:=((mem_square_div (Q.side_pos hA)).mp hzQ) i
    have hf:=((mem_square_div (F.side_pos hA)).mp hzF) i
    rw [Cell.side,hlevel] at hq
    exact hq.symm.trans hf
  exact Cell.ext hlevel hp

lemma square_subset_large_neighborhood {s t D : ℕ} {p q : Point} (hst : s≤t)
    {y : Point} (hy : y∈neighborhood D s p) (hy' : y∈neighborhood D t q) :
    square s p⊆neighborhood (2*D+1) t q := by
  have hst' : (s:ℤ)≤t := by exact_mod_cast hst
  have hD : (0:ℤ)≤D := Int.natCast_nonneg D
  intro z hz
  apply mem_neighborhood.mpr
  intro i
  have h1:=mem_neighborhood.mp hy i
  have h2:=mem_neighborhood.mp hy' i
  have h3:=mem_square.mp hz i
  push_cast
  constructor <;> nlinarith

end SharpNodal.Grid

namespace SharpNodal.Grid

lemma Cell.rank_strict {A : ℕ} {F : Finset Cell} {Q P : Cell} (hP : P∈F)
    (hlev : Q.level<P.level) (hsub : Q.points A⊆P.points A) : P.rank A F<Q.rank A F := by
  have hsubset : P.ancestors A F⊆Q.ancestors A F := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hS,hlevS,hsubS⟩
    exact Finset.mem_filter.mpr ⟨hS,hlev.trans hlevS,hsub.trans hsubS⟩
  have hne : P.ancestors A F≠Q.ancestors A F := by
    intro he
    have hh:P∈Q.ancestors A F := Finset.mem_filter.mpr ⟨hP,hlev,hsub⟩
    rw [←he] at hh
    exact (lt_irrefl P.level) (Finset.mem_filter.mp hh).2.1
  have hc:=Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset,hne⟩)
  exact Nat.add_lt_add_left hc 1

lemma Cell.same_rank_disjoint {A : ℕ} (hA : 0<A) {F : Finset Cell} {Q P : Cell}
    (hQ : Q∈F) (hP : P∈F) (hr : Q.rank A F=P.rank A F) (hne : Q≠P) :
    Disjoint (Q.points A) (P.points A) := by
  apply Finset.disjoint_left.mpr
  intro z hzQ hzP
  rcases lt_trichotomy Q.level P.level with hlev|hlev|hlev
  · have hh:=Cell.rank_strict hP hlev (Cell.subset_of_intersection hA hlev.le hzQ hzP)
    omega
  · exact hne (Cell.equal_level_eq_of_intersection hA hlev hzQ hzP)
  · have hh:=Cell.rank_strict hQ hlev (Cell.subset_of_intersection hA hlev.le hzP hzQ)
    omega

lemma card_le_add_symmDiff {X : Type*} [DecidableEq X] (S T : Finset X) :
    S.card≤T.card+(S ∆ T).card := by
  have hsub : S⊆T∪(S ∆ T) := by
    intro x hx
    by_cases ht:x∈T
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (by simp [Finset.mem_symmDiff,hx,ht])
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma Cell.rank_control {A J : ℕ} (hA : 0<A) (F : Finset Cell) (Q : Cell) (x : Point)
    (hsmall : (Q.smallerAt A F x).card≤J) :
    Q.rank A F≤totalAt A F x+Q.mismatch A F x+J+1 ∧
      totalAt A F x≤Q.rank A F+Q.mismatch A F x+J+1 := by
  have ha:=card_le_add_symmDiff (Q.ancestors A F) (Q.largerAt A F x)
  have hb:=card_le_add_symmDiff (Q.largerAt A F x) (Q.ancestors A F)
  rw [symmDiff_comm] at hb
  let Equal:=F.filter (fun P =>Q.level=P.level ∧ x∈P.points A)
  have he : Equal.card≤1 := by
    apply Finset.card_le_one.mpr
    intro P hP S hS
    rcases Finset.mem_filter.mp hP with ⟨_,hP,hxP⟩
    rcases Finset.mem_filter.mp hS with ⟨_,hS,hxS⟩
    exact Cell.equal_level_eq_of_intersection hA (hP.symm.trans hS) hxP hxS
  have hsum : totalAt A F x=(Q.largerAt A F x).card+Equal.card+(Q.smallerAt A F x).card := by
    simp only [totalAt,Cell.largerAt,Cell.smallerAt,Equal,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hx : x∈P.points A
    · simp only [hx,and_true,ite_true]
      split_ifs <;> omega
    · simp only [hx,and_false,ite_false,add_zero]
  dsimp only [Cell.rank,Cell.mismatch]
  omega

end SharpNodal.Grid

noncomputable section
open scoped BigOperators
open Set
namespace SharpNodal.Grid

theorem finite_greedy {Q X : Type*} [DecidableEq Q] [DecidableEq X]
    (F : Finset Q) (size : Q → ℕ) (B : Q → Finset X)
    (hB : ∀q∈F,(B q).Nonempty) :
    ∃S : Finset Q,S⊆F ∧ (S : Set Q).Pairwise (fun q p =>Disjoint (B q) (B p)) ∧
      ∀q∈F,∃p∈S,size q ≤ size p ∧ ¬Disjoint (B q) (B p) := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hF : F.Nonempty
    · obtain ⟨p,hp,hmax⟩:=Finset.exists_max_image F size hF
      let G:=F.filter (fun q =>Disjoint (B q) (B p))
      have hGp : p∉G := by
        intro hh
        have hd:Disjoint (B p) (B p):=(Finset.mem_filter.mp hh).2
        obtain ⟨x,hx⟩:=hB p hp
        exact Finset.disjoint_left.mp hd hx hx
      have hGF : G⊂F := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,by
        intro he
        exact hGp (he.symm ▸ hp)⟩
      obtain ⟨S,hSG,hdis,hcover⟩:=ih G hGF (fun q hq =>hB q (Finset.mem_filter.mp hq).1)
      refine ⟨insert p S,?_,?_,?_⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl|hq
        · exact hp
        · exact (Finset.mem_filter.mp (hSG hq)).1
      · intro q hq q' hq' hne
        by_cases he : q=p
        · subst q
          have hqS : q'∈S := (Finset.mem_insert.mp hq').resolve_left (Ne.symm hne)
          exact ((Finset.mem_filter.mp (hSG hqS)).2).symm
        · have hqS : q∈S := (Finset.mem_insert.mp hq).resolve_left he
          by_cases he' : q'=p
          · subst q'
            exact (Finset.mem_filter.mp (hSG hqS)).2
          · have hq'S : q'∈S := (Finset.mem_insert.mp hq').resolve_left he'
            exact hdis hqS hq'S hne
      · intro q hq
        by_cases hqG : q∈G
        · obtain ⟨q',hq',hs,hd⟩:=hcover q hqG
          exact ⟨q',Finset.mem_insert_of_mem hq',hs,hd⟩
        · refine ⟨p,Finset.mem_insert_self _ _,hmax q hq,?_⟩
          exact fun hd =>hqG (Finset.mem_filter.mpr ⟨hq,hd⟩)
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      subst F
      exact ⟨∅,by simp,by simp,by simp⟩

lemma disjoint_cover_card {Q X : Type*} [DecidableEq Q] [DecidableEq X]
    (F S : Finset Q) (C B : Q → Finset X)
    (hdis : (F : Set Q).Pairwise (fun q p =>Disjoint (C q) (C p)))
    (hcover : ∀q∈F,∃p∈S,C q⊆B p) :
    (∑q∈F,(C q).card)≤∑p∈S,(B p).card := by
  calc
    _=(F.biUnion C).card := (Finset.card_biUnion hdis).symm
    _≤(S.biUnion B).card := Finset.card_le_card (by
      intro x hx
      obtain ⟨q,hq,hx⟩:=Finset.mem_biUnion.mp hx
      obtain ⟨p,hp,hsub⟩:=hcover q hq
      exact Finset.mem_biUnion.mpr ⟨p,hp,hsub hx⟩)
    _≤_ := Finset.card_biUnion_le

end SharpNodal.Grid
namespace SharpNodal.Grid

theorem rank_selection {A D : ℕ} (hA : 0<A) (F : Finset Cell) :
    ∃S : Finset Cell,S⊆F ∧
      (∀Q∈S,∀P∈S,Q.rank A F=P.rank A F → Q≠P → Disjoint (Q.near A D) (P.near A D)) ∧
      (∑Q∈F,(Q.points A).card)≤(4*D+3)^2*∑Q∈S,(Q.points A).card := by
  classical
  let R:=F.image (Cell.rank A F)
  let Fr : ℕ → Finset Cell := fun n =>F.filter (fun Q =>Q.rank A F=n)
  have hchoose (n : ℕ) := finite_greedy (Fr n) Cell.level (Cell.near A D) (fun Q _ =>
    Finset.card_pos.mp (by rw [Cell.card_near]; exact pow_pos (Nat.mul_pos (by omega) (Q.side_pos hA)) 2))
  choose S hsub hdis hcover using hchoose
  let T:=R.biUnion S
  have hTF : T⊆F := by
    intro Q hQ
    obtain ⟨r,hr,hQ⟩:=Finset.mem_biUnion.mp hQ
    exact (Finset.mem_filter.mp (hsub r hQ)).1
  have hTin (Q : Cell) (hQ : Q∈T) : Q∈S (Q.rank A F) := by
    obtain ⟨r,hr,hQ⟩:=Finset.mem_biUnion.mp hQ
    have he:= (Finset.mem_filter.mp (hsub r hQ)).2
    exact he.symm ▸ hQ
  have hSS : (R : Set ℕ).Pairwise (fun r s =>Disjoint (S r) (S s)) := by
    intro r hr s hs hne
    apply Finset.disjoint_left.mpr
    intro Q hQ hQ'
    have he:=(Finset.mem_filter.mp (hsub r hQ)).2
    have he':=(Finset.mem_filter.mp (hsub s hQ')).2
    exact hne (he.symm.trans he')
  have hbound (r : ℕ) : (∑Q∈Fr r,(Q.points A).card)≤(4*D+3)^2*∑Q∈S r,(Q.points A).card := by
    have hpd : (Fr r : Set Cell).Pairwise (fun Q P =>Disjoint (Q.points A) (P.points A)) := by
      intro Q hQ P hP hne
      rcases Finset.mem_filter.mp hQ with ⟨hQ,hrQ⟩
      rcases Finset.mem_filter.mp hP with ⟨hP,hrP⟩
      exact Cell.same_rank_disjoint hA hQ hP (hrQ.trans hrP.symm) hne
    have hh:=disjoint_cover_card (Fr r) (S r) (Cell.points A) (Cell.near A (2*D+1)) hpd (by
      intro Q hQ
      obtain ⟨P,hP,hlev,hmeet⟩:=hcover r Q hQ
      obtain ⟨y,hyQ,hyP⟩:=Finset.not_disjoint_iff.mp hmeet
      exact ⟨P,hP,square_subset_large_neighborhood (Q.side_mono hA hlev) hyQ hyP⟩)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [Cell.card_near,Cell.card_points]
    ring
  refine ⟨T,hTF,?_,?_⟩
  · intro Q hQ P hP hr hne
    apply hdis (Q.rank A F) (hTin Q hQ) _ hne
    rw [hr]
    exact hTin P hP
  · have hfib:=Finset.sum_fiberwise_of_maps_to (s:=F) (t:=R)
      (fun Q hQ =>Finset.mem_image_of_mem (Cell.rank A F) hQ) (fun Q =>(Q.points A).card)
    calc
      _=∑r∈R,∑Q∈Fr r,(Q.points A).card := hfib.symm
      _≤∑r∈R,(4*D+3)^2*∑Q∈S r,(Q.points A).card := Finset.sum_le_sum (fun r _ =>hbound r)
      _=(4*D+3)^2*∑r∈R,∑Q∈S r,(Q.points A).card := (Finset.mul_sum _ _ _).symm
      _=_ := by rw [←Finset.sum_biUnion hSS]

end SharpNodal.Grid

namespace SharpNodal.Grid

lemma card_strip (s h : ℕ) (p : Point) (i : Fin 2) (upper : Bool) :
    (strip s h p i upper).card=2*h*(s+2*h) := by
  have hlow (j : Fin 2) : (p j*(s:ℤ)+h-(p j*s-h)).toNat=2*h := by
    have he:p j*(s:ℤ)+h-(p j*s-h)=((2*h:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have hhigh (j : Fin 2) : ((p j+1)*(s:ℤ)+h-((p j+1)*s-h)).toNat=2*h := by
    have he:(p j+1)*(s:ℤ)+h-((p j+1)*s-h)=((2*h:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have hfull (j : Fin 2) : ((p j+1)*(s:ℤ)+h-(p j*s-h)).toNat=s+2*h := by
    have he:(p j+1)*(s:ℤ)+h-(p j*s-h)=((s+2*h:ℕ):ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  rw [strip,card_box,Fin.prod_univ_two]
  fin_cases i <;> cases upper
  · change (p 0*(s:ℤ)+h-(p 0*s-h)).toNat * ((p 1+1)*(s:ℤ)+h-(p 1*s-h)).toNat = _
    rw [hlow,hfull]
  · change ((p 0+1)*(s:ℤ)+h-((p 0+1)*s-h)).toNat * ((p 1+1)*(s:ℤ)+h-(p 1*s-h)).toNat = _
    rw [hhigh,hfull]
  · change ((p 0+1)*(s:ℤ)+h-(p 0*s-h)).toNat * (p 1*(s:ℤ)+h-(p 1*s-h)).toNat = _
    rw [hfull,hlow,mul_comm]
  · change ((p 0+1)*(s:ℤ)+h-(p 0*s-h)).toNat * ((p 1+1)*(s:ℤ)+h-((p 1+1)*s-h)).toNat = _
    rw [hfull,hhigh,mul_comm]

lemma card_border_le (s h : ℕ) (p : Point) : (border s h p).card≤8*s*h+16*h^2 := by
  calc
    _≤∑ib : Fin 2 × Bool,(strip s h p ib.1 ib.2).card := Finset.card_biUnion_le
    _=8*s*h+16*h^2 := by simp only [card_strip,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,smul_eq_mul]; ring

lemma mem_border_of {s h : ℕ} {p z : Point} (hz : z∈expanded s h p)
    (hedge : ∃i,z i<p i*s+h ∨ (p i+1)*s-h≤z i) : z∈border s h p := by
  obtain ⟨i,hi⟩:=hedge
  rcases hi with hi|hi
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i,false),Finset.mem_univ _,?_⟩
    apply mem_box.mpr
    intro j
    have hh:=mem_box.mp hz j
    simp only [Bool.false_and,Bool.not_false,Bool.true_and,Bool.false_eq_true,ite_false,decide_eq_true_eq]
    by_cases hji:j=i
    · subst j
      simp only [↓reduceIte]
      exact ⟨hh.1,hi⟩
    · simp only [hji,↓reduceIte]
      exact hh
  · apply Finset.mem_biUnion.mpr
    refine ⟨(i,true),Finset.mem_univ _,?_⟩
    apply mem_box.mpr
    intro j
    have hh:=mem_box.mp hz j
    simp only [Bool.true_and,Bool.not_true,Bool.false_and,Bool.false_eq_true,ite_false,decide_eq_true_eq]
    by_cases hji:j=i
    · subst j
      simp only [↓reduceIte]
      exact ⟨hi,hh.2⟩
    · simp only [hji,↓reduceIte]
      exact hh

lemma square_subset_expanded (s h : ℕ) (p : Point) : square s p⊆expanded s h p := by
  apply box_mono <;> intro i <;> omega

lemma Cell.mismatch_collar {A D : ℕ} (hA : 0<A) {Q F : Cell} (hlev : Q.level≤F.level)
    {y : Point} (hy : y∈Q.near A D)
    (hmis : (Q.points A⊆F.points A ∧ y∉F.points A) ∨
      (¬Q.points A⊆F.points A ∧ y∈F.points A)) :
    Q.points A⊆border (F.side A) ((D+1)*Q.side A) F.pos := by
  let s:=Q.side A
  let t:=F.side A
  have hs : (0:ℤ) < s := by exact_mod_cast Q.side_pos hA
  have ht : (0:ℤ)<t := by exact_mod_cast F.side_pos hA
  have hD : (0:ℤ)≤D := Int.natCast_nonneg D
  have hy' : ∀i,(Q.pos i-D)*s≤y i ∧ y i<(Q.pos i+1+D)*s := mem_neighborhood.mp hy
  intro z hz
  have hz' : ∀i,Q.pos i*s≤z i ∧ z i<(Q.pos i+1)*s := mem_square.mp hz
  apply mem_border_of
  · rcases hmis with ⟨hsub,hout⟩|⟨hnsub,hin⟩
    · exact square_subset_expanded _ _ _ (hsub hz)
    · apply mem_box.mpr
      intro i
      have hin':=mem_square.mp hin i
      have h1:=hy' i
      have h2:=hz' i
      change F.pos i*t-((D+1)*s:ℕ)≤z i ∧ z i<(F.pos i+1)*t+((D+1)*s:ℕ)
      push_cast
      constructor <;> nlinarith
  · rcases hmis with ⟨hsub,hout⟩|⟨hnsub,hin⟩
    · have hout' : ¬∀i,F.pos i*t≤y i ∧ y i<(F.pos i+1)*t := by simpa only [Cell.points,mem_square] using hout
      obtain ⟨i,hi⟩:=not_forall.mp hout'
      refine ⟨i,?_⟩
      have h1:=hy' i
      have h2:=hz' i
      change z i<F.pos i*t+((D+1)*s:ℕ) ∨ (F.pos i+1)*t-((D+1)*s:ℕ)≤z i
      push_cast
      by_cases hh : y i<F.pos i*t
      · exact Or.inl (by nlinarith)
      · have hh' : (F.pos i+1)*t≤y i := by omega
        exact Or.inr (by nlinarith)
    · have hdis:= (Cell.subset_or_disjoint hA hlev).resolve_left hnsub
      have hzout : z∉F.points A := fun hzF =>Finset.disjoint_left.mp hdis hz hzF
      have hzout' : ¬∀i,F.pos i*t≤z i ∧ z i<(F.pos i+1)*t := by simpa only [Cell.points,mem_square] using hzout
      obtain ⟨i,hi⟩:=not_forall.mp hzout'
      refine ⟨i,?_⟩
      change z i<F.pos i*t+((D+1)*s:ℕ) ∨ (F.pos i+1)*t-((D+1)*s:ℕ)≤z i
      have hh : (0:ℤ)≤((D+1)*s:ℕ) := Int.natCast_nonneg _
      omega

end SharpNodal.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_WitnessPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set

namespace SharpNodal.Grid

lemma sum_powers_le {A : ℕ} (hA : 2≤A) (n : ℕ) : (∑i∈Finset.range n,A^i)≤A^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,pow_succ]
    calc
      _≤A^n+A^n := Nat.add_le_add_right ih _
      _=A^n*2 := by omega
      _≤A^n*A := Nat.mul_le_mul_left _ hA

lemma sum_squared_powers_le {A : ℕ} (hA : 2≤A) (n : ℕ) :
    (∑i∈Finset.range n,(A^i)^2)≤(A^n)^2 := by
  have hh:=sum_powers_le (A:=A^2) (by nlinarith) n
  simpa only [←pow_mul,mul_comm] using hh

lemma Cell.mem_mismatch_set {A : ℕ} {F : Finset Cell} {Q P : Cell} {x : Point} :
    P∈Q.ancestors A F ∆ Q.largerAt A F x ↔ P∈F ∧ Q.level<P.level ∧
      ((Q.points A⊆P.points A ∧ x∉P.points A) ∨ (¬Q.points A⊆P.points A ∧ x∈P.points A)) := by
  simp only [Finset.mem_symmDiff,Cell.ancestors,Cell.largerAt,Finset.mem_filter]
  tauto

lemma Cell.mismatch_set_subset {A : ℕ} (F : Finset Cell) (Q : Cell) (x : Point) :
    Q.ancestors A F ∆ Q.largerAt A F x⊆F := by
  intro P hP
  exact (Cell.mem_mismatch_set.mp hP).1

lemma mismatch_at_scale {A D : ℕ} (hA : 0<A) (F S : Finset Cell) (Y : Cell → Finset Point)
    (hY : ∀Q∈S,Y Q⊆Q.near A D) (P : Cell) (n : ℕ) :
    (∑Q∈S.filter (fun Q =>Q.level=n),(Y Q |>.filter (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x)).card)
      ≤(2*D+1)^2*(8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2) := by
  classical
  let Bad : Cell → Finset Point := fun Q =>(Y Q).filter (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x)
  let T:=S.filter (fun Q =>Q.level=n)
  let G:=T.filter (fun Q =>(Bad Q).Nonempty)
  have hGT : G⊆T := Finset.filter_subset _ _
  have hGS : G⊆S := hGT.trans (Finset.filter_subset _ _)
  have heq : (∑Q∈G,(Bad Q).card)=(∑Q∈T,(Bad Q).card) := by
    apply Finset.sum_subset hGT
    intro Q hQ hn
    have hbad : ¬(Bad Q).Nonempty := fun h =>hn (Finset.mem_filter.mpr ⟨hQ,h⟩)
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hbad)
  have hdis : (G : Set Cell).Pairwise (fun Q Q' =>Disjoint (Q.points A) (Q'.points A)) := by
    intro Q hQ Q' hQ' hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    have he : Q.level=Q'.level := (Finset.mem_filter.mp (hGT hQ)).2.trans (Finset.mem_filter.mp (hGT hQ')).2.symm
    exact hne (Cell.equal_level_eq_of_intersection hA he hz hz')
  have hcollar (Q : Cell) (hQ : Q∈G) : Q.points A⊆border (P.side A) ((D+1)*A^n) P.pos := by
    obtain ⟨x,hx⟩:=(Finset.mem_filter.mp hQ).2
    rcases Finset.mem_filter.mp hx with ⟨hx,hmis⟩
    rcases Cell.mem_mismatch_set.mp hmis with ⟨_,hlev,hmis⟩
    have hh:=Cell.mismatch_collar hA hlev.le (hY Q (hGS hQ) hx) hmis
    simpa only [Cell.side,(Finset.mem_filter.mp (hGT hQ)).2] using hh
  have hcard : (∑Q∈G,(Q.points A).card)≤(border (P.side A) ((D+1)*A^n) P.pos).card := by
    rw [←Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨Q,hQ,hz⟩:=Finset.mem_biUnion.mp hz
    exact hcollar Q hQ hz
  have hbadcard (Q : Cell) (hQ : Q∈G) : (Bad Q).card≤(2*D+1)^2*(Q.points A).card := by
    have hh : (Bad Q).card ≤ (Q.near A D).card := Finset.card_le_card
      ((Finset.filter_subset (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x) (Y Q)).trans (hY Q (hGS hQ)))
    change (Bad Q).card≤(Q.near A D).card at hh
    simpa only [Cell.card_near,Cell.card_points,mul_pow] using hh
  change (∑Q∈T,(Bad Q).card)≤_
  rw [←heq]
  calc
    _≤∑Q∈G,(2*D+1)^2*(Q.points A).card := Finset.sum_le_sum (fun Q hQ =>hbadcard Q hQ)
    _=(2*D+1)^2*∑Q∈G,(Q.points A).card := (Finset.mul_sum _ _ _).symm
    _≤(2*D+1)^2*(border (P.side A) ((D+1)*A^n) P.pos).card := Nat.mul_le_mul_left _ hcard
    _≤_ := Nat.mul_le_mul_left _ (card_border_le _ _ _)

lemma mismatch_for_larger {A D : ℕ} (hA : 2≤A) (F S : Finset Cell) (Y : Cell → Finset Point)
    (hY : ∀Q∈S,Y Q⊆Q.near A D) (P : Cell) :
    (∑Q∈S,(Y Q |>.filter (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x)).card)
      ≤ mismatchConstant D*(P.points A).card := by
  classical
  let Bad : Cell → Finset Point := fun Q =>(Y Q).filter (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x)
  have hfib : (∑Q∈S,(Bad Q).card)=∑n∈Finset.range P.level,∑Q∈S.filter (fun Q =>Q.level=n),(Bad Q).card := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro Q hQ hn
    have hlev : ¬Q.level<P.level := by simpa only [Finset.mem_filter,hQ,Finset.mem_range,true_and] using hn
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hlev (Cell.mem_mismatch_set.mp (Finset.mem_filter.mp hx).2).2.1
  have hscale:=fun n =>mismatch_at_scale (by omega : 0<A) F S Y hY P n
  have hsum : (∑n∈Finset.range P.level,(8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2))
      =(8*(D+1)*P.side A)*(∑n∈Finset.range P.level,A^n)+
        (16*(D+1)^2)*(∑n∈Finset.range P.level,(A^n)^2) := by
    have he (n : ℕ) : 8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2=
        (8*(D+1)*P.side A)*A^n+(16*(D+1)^2)*(A^n)^2 := by ring
    simp_rw [he,Finset.sum_add_distrib,←Finset.mul_sum]
  have hbound : (∑n∈Finset.range P.level,(8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2))
      ≤(8*(D+1)+16*(D+1)^2)*(P.side A)^2 := by
    rw [hsum]
    calc
      _≤(8*(D+1)*P.side A)*(P.side A)+(16*(D+1)^2)*(P.side A)^2 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (sum_powers_le hA P.level))
          (Nat.mul_le_mul_left _ (sum_squared_powers_le hA P.level))
      _=_ := by ring
  change (∑Q∈S,(Bad Q).card)≤_
  rw [hfib]
  calc
    _≤∑n∈Finset.range P.level,(2*D+1)^2*(8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2) :=
      Finset.sum_le_sum (fun n _ =>hscale n)
    _=(2*D+1)^2*∑n∈Finset.range P.level,(8*P.side A*((D+1)*A^n)+16*((D+1)*A^n)^2) :=
      (Finset.mul_sum _ _ _).symm
    _≤(2*D+1)^2*((8*(D+1)+16*(D+1)^2)*(P.side A)^2) := Nat.mul_le_mul_left _ hbound
    _=_ := by rw [Cell.card_points,mismatchConstant]; ring

theorem total_mismatch_bound {A D : ℕ} (hA : 2≤A) (F S : Finset Cell) (Y : Cell → Finset Point)
    (hY : ∀Q∈S,Y Q⊆Q.near A D) :
    (∑Q∈S,∑x∈Y Q,Q.mismatch A F x)≤ mismatchConstant D*∑P∈F,(P.points A).card := by
  classical
  have hQ (Q : Cell) : (∑x∈Y Q,Q.mismatch A F x)=
      ∑P∈F,(Y Q |>.filter (fun x =>P∈Q.ancestors A F ∆ Q.largerAt A F x)).card := by
    have hh:=Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=Y Q) (t:=F)
      (fun x P =>P∈Q.ancestors A F ∆ Q.largerAt A F x)
    simp only [Finset.bipartiteAbove,Finset.bipartiteBelow] at hh
    rw [←hh]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only [Cell.mismatch]
    congr 1
    ext P
    simp only [Finset.mem_filter]
    exact ⟨fun h =>⟨Q.mismatch_set_subset F x h,h⟩,fun h =>h.2⟩
  simp_rw [hQ]
  rw [Finset.sum_comm]
  calc
    _≤∑P∈F,mismatchConstant D*(P.points A).card :=
      Finset.sum_le_sum (fun P _ =>mismatch_for_larger hA F S Y hY P)
    _=_ := (Finset.mul_sum _ _ _).symm

end SharpNodal.Grid

namespace SharpNodal.Grid

theorem nearby_witness_packing {A D c J : ℕ} (hA : 2≤A) (F : Finset Cell)
    (root : Cell) (Y : Cell → Finset Point)
    (hroot : ∀Q∈F,Q.level ≤ root.level ∧ Q.points A⊆root.points A)
    (hnear : ∀Q∈F,Y Q⊆Q.near A D)
    (hlower : ∀Q∈F,(Q.points A).card ≤ c*(Y Q).card)
    (hsmall : ∀Q∈F,∀x∈Y Q,(Q.smallerAt A F x).card≤J) :
    (∑Q∈F,(Q.points A).card) ≤ packingConstant D c J*(root.points A).card := by
  classical
  obtain ⟨S,hSF,hdis,hweight⟩:=rank_selection (A:=A) (D:=D) (by omega) F
  let W:=∑Q∈F,(Q.points A).card
  let c':=(4*D+3)^2*c
  have hlower' : W ≤ c'*∑Q∈S,(Y Q).card := by
    calc
      _≤(4*D+3)^2*∑Q∈S,(Q.points A).card := hweight
      _≤(4*D+3)^2*∑Q∈S,c*(Y Q).card :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun Q hQ =>hlower Q (hSF hQ)))
      _=_ := by rw [←Finset.mul_sum]; exact (Nat.mul_assoc _ _ _).symm
  have hambient : ∀Q∈S,Y Q⊆root.near A D := by
    intro Q hQ
    exact (hnear Q (hSF hQ)).trans (Cell.near_mono (by omega) (hroot Q (hSF hQ)).1 (hroot Q (hSF hQ)).2)
  have hdis' : ∀Q∈S,∀P∈S,Q.rank A F=P.rank A F → Q≠P → Disjoint (Y Q) (Y P) := by
    intro Q hQ P hP hr hne
    exact (hdis Q hQ P hP hr hne).mono (hnear Q (hSF hQ)) (hnear P (hSF hP))
  have hrank : ∀Q∈S,∀x∈Y Q,Q.rank A F≤totalAt A F x+Q.mismatch A F x+J+1 ∧
      totalAt A F x≤Q.rank A F+Q.mismatch A F x+J+1 := by
    intro Q hQ x hx
    exact Cell.rank_control (by omega) F Q x (hsmall Q (hSF hQ) x hx)
  have hh:=finite_witness_packing S (root.near A D) Y (Cell.rank A F) (totalAt A F)
    (Cell.mismatch A F) W c' (mismatchConstant D) J hlower'
    (total_mismatch_bound hA F S Y (fun Q hQ =>hnear Q (hSF hQ))) hambient hdis' hrank
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [Cell.card_near,Cell.card_points]
  dsimp only [packingConstant,c']
  ring

end SharpNodal.Grid

end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_Excursions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set

namespace SharpNodal.Profiles

lemma UnitWave.growth_zero {Cp a₀ : ℝ} (D : UnitWave Cp a₀) :
    D.growth 0=fieldGrowth D.U D.K := by simp only [UnitWave.growth,UnitWave.excess,smul_zero,fieldGrowth]

lemma HighWavePath.raw {A : ℕ} {Cp a₀ L : ℝ} {n : ℕ} {D : ScaledWave Cp a₀}
    {w : GridWord A n} (h : HighWavePath A L n D w) : PathHigh A L n D.U D.K w := by
  induction n generalizing D with
  | zero => simpa only [HighWavePath,PathHigh,UnitWave.growth_zero] using h
  | succ n ih =>
    rcases h with ⟨h,E,hE,hh⟩
    refine ⟨by simpa only [UnitWave.growth_zero] using h,?_⟩
    have hh':=ih hh
    rw [hE.2.1,hE.2.2.1] at hh'
    exact hh'

namespace WaveTree
variable {A : ℕ} {Cp a₀ : ℝ}

theorem build_untilted_stopped {C₀ C₁ L : ℝ} (hA : 2≤A) (ha₀ : 0<a₀) (hC₀ : 0≤C₀)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (n : ℕ) (D : ScaledWave Cp a₀) (b : Plane)
    (hbottom : a₀≤D.K/(A:ℝ)^n) :
    ∃t : WaveTree A Cp a₀,t.rootWave=D ∧ t.rootTilt=b ∧ Coherent n t ∧
      Descent.Tree.Valid C₁ (t.numerical C₀) ∧ StopsAtLow L n t := by
  classical
  have hAr : 2≤(A:ℝ) := by exact_mod_cast hA
  have hArpos : 0<(A:ℝ) := by linarith
  induction n generalizing D b with
  | zero => exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,trivial⟩
  | succ n ih =>
    by_cases hP : L<D.growth 0
    · have hid : (D.K/(A:ℝ))/(A:ℝ)^n=D.K/(A:ℝ)^(n+1) := by rw [pow_succ]; ring
      have hnext : a₀≤D.K/(A:ℝ) := by
        have hpow : 1≤(A:ℝ)^n := one_le_pow₀ (by linarith)
        have hh := (le_div_iff₀ (pow_pos hArpos n)).mp (hid.symm ▸ hbottom)
        exact (le_mul_of_one_le_right ha₀.le hpow).trans hh
      obtain ⟨E,b',hchild,hinc,hdec⟩ := hrule D b hnext (Or.inl hP)
      have hbot (i : GridIndex A) : a₀≤(E i).K/(A:ℝ)^n := by rw [(hchild i).2.2.1,hid]; exact hbottom
      choose t hroot htilt hcoh hvalid hstop using (fun i =>ih (E i) (b' i) (hbot i))
      refine ⟨.step D b t,rfl,rfl,?_,?_,⟨hP,hstop⟩⟩
      · intro i
        rw [hroot i]
        exact ⟨hchild i,hcoh i⟩
      · refine ⟨(label_nonnegative ha₀ hC₀ D b).1,(label_nonnegative ha₀ hC₀ D b).2,?_,?_,hvalid⟩
        · simpa only [numerical_root,hroot,htilt,label] using hdec
        · simpa only [numerical_root,hroot,htilt,label] using hinc
    · exact ⟨.stop D b,rfl,rfl,trivial,label_nonnegative ha₀ hC₀ D b,le_of_not_gt hP⟩

lemma active_average_le_cost {C₀ C₁ L : ℝ} (hA : 0<A) (ha₀ : 0<a₀)
    (n : ℕ) (t : WaveTree A Cp a₀) (hcoh : t.Coherent n)
    (hvalid : Descent.Tree.Valid C₁ (t.numerical C₀)) (hstop : t.StopsAtLow L n) :
    (𝔼 w : GridWord A n,activeGrowth A L n t.rootWave.U t.rootWave.K w)≤
      (t.numerical C₀).massCost+1001*(‖t.rootTilt‖+(t.numerical C₀).tiltCost) := by
  have : NeZero A := ⟨hA.ne'⟩
  induction n generalizing t with
  | zero => cases t with
    | stop D b =>
      have hg : D.growth 0≤D.growth b+1001*‖b‖ := by
        have hh:=D.toUnitWave.growth_change ha₀ 0 b
        simpa only [zero_sub,norm_neg] using hh
      change (𝔼 w : GridWord A 0,activeGrowth A L 0 D.U D.K w)≤D.growth b+1001*(‖b‖+0)
      by_cases hh : L<fieldGrowth D.U D.K
      · simp only [activeGrowth,PathHigh,pathGrowth,hh,ite_true,Fintype.expect_const,add_zero]
        simpa only [UnitWave.growth_zero] using hg
      · simp only [activeGrowth,PathHigh,pathGrowth,hh,ite_false,Fintype.expect_const,add_zero]
        have hh:=D.toUnitWave.growth_nonneg ha₀ b
        positivity
    | step D b ts =>exact hcoh.elim
  | succ n ih =>cases t with
    | stop D b =>
      have hl : fieldGrowth D.U D.K≤L := by simpa only [StopsAtLow,UnitWave.growth_zero] using hstop
      have hh (w : GridWord A (n+1)) : activeGrowth A L (n+1) D.U D.K w=0 := by
        simp [activeGrowth,PathHigh,not_lt.mpr hl]
      change (𝔼 w : GridWord A (n+1),activeGrowth A L (n+1) D.U D.K w)≤D.growth b+1001*(‖b‖+0)
      simp only [hh,Fintype.expect_const,add_zero]
      have hm:=D.toUnitWave.growth_nonneg ha₀ b
      positivity
    | step D b ts =>
      have hhigh : L<fieldGrowth D.U D.K := by simpa only [UnitWave.growth_zero] using hstop.1
      have hrewrite (i : GridIndex A) (w : GridWord A n) :
          activeGrowth A L (n+1) D.U D.K (Fin.cons i w)=
            activeGrowth A L n (ts i).rootWave.U (ts i).rootWave.K w := by
        rw [(hcoh i).1.2.1,(hcoh i).1.2.2.1]
        simp only [activeGrowth,PathHigh,pathGrowth,Fin.cons_zero,Fin.tail_cons,hhigh,true_and]
      have havg:=Finset.expect_le_expect (s:=Finset.univ) (fun i _ =>
        ih (ts i) (hcoh i).2 (hvalid.2.2.2.2 i) (hstop.2 i))
      have htri:=Finset.expect_le_expect (s:=Finset.univ) (fun i (_ : i∈(Finset.univ : Finset (GridIndex A))) =>
        show ‖(ts i).rootTilt‖≤‖(ts i).rootTilt-b‖+‖b‖ from by
          simpa only [sub_add_cancel] using norm_add_le ((ts i).rootTilt-b) b)
      simp only [Finset.expect_add_distrib,←Finset.mul_expect,Fintype.expect_const] at havg htri
      have hn : 0≤D.growth b := hvalid.1
      change (𝔼 w : GridWord A (n+1),activeGrowth A L (n+1) D.U D.K w)≤_
      rw [expect_word_succ]
      simp_rw [hrewrite]
      simp only [numerical,Descent.Tree.massCost,Descent.Tree.tiltCost,numerical_root,label,rootTilt]
      change (𝔼 i,𝔼 w : GridWord A n,activeGrowth A L n (ts i).rootWave.U (ts i).rootWave.K w)≤
        D.growth b+(𝔼 i,(numerical C₀ (ts i)).massCost)+1001*(‖b‖+
          𝔼 i,(‖(ts i).rootTilt-b‖+(numerical C₀ (ts i)).tiltCost))
      rw [Finset.expect_add_distrib]
      linarith

end WaveTree
end SharpNodal.Profiles

namespace SharpNodal.Profiles

lemma excursionCostConstant_nonneg {C₀ C₁ a₀ : ℝ}
    (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (ha₀ : 0<a₀) : 0≤excursionCostConstant C₀ C₁ a₀ := by
  dsimp [excursionCostConstant]
  positivity

theorem active_terminal_average {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (n : ℕ) (D : ScaledWave Cp a₀)
    (hbottom : a₀≤D.K/(A:ℝ)^n) :
    (𝔼 w : GridWord A n,activeGrowth A L n D.U D.K w)≤
      excursionCostConstant C₀ C₁ a₀*(D.growth 0+1) := by
  have : NeZero A := ⟨by omega⟩
  obtain ⟨t,hD,hb,hcoh,hvalid,hstop⟩:=WaveTree.build_untilted_stopped hA ha₀ hC₀ hrule n D 0 hbottom
  have hc:=WaveTree.active_average_le_cost (by omega : 0<A) ha₀ n t hcoh hvalid hstop
  rw [hD,hb,norm_zero,zero_add] at hc
  have hscaled:=t.coherent_floors C₀ hcoh
  rw [hD] at hscaled
  have hf:=Descent.Tree.physical_floor_bound (by exact_mod_cast hA : (2:ℝ)≤A) hC₀ ha₀
    (ha₀.trans_le D.frequency_lower) D.side_pos.le D.side_le_one n hbottom hscaled
  obtain ⟨hm,ht⟩:=Descent.Tree.stopped_descent hC₁ hvalid
  rw [WaveTree.numerical_root,hD,hb] at hm ht
  change (t.numerical C₀).massCost≤2*D.growth 0+(t.numerical C₀).floorCost at hm
  change (t.numerical C₀).tiltCost≤2*C₁*D.growth 0+2*C₁*(t.numerical C₀).floorCost at ht
  have hF : 0≤2*(C₀/a₀+1) := by positivity
  have hh : (𝔼 w : GridWord A n,activeGrowth A L n D.U D.K w)≤
      (2+2002*C₁)*D.growth 0+(1+2002*C₁)*(2*(C₀/a₀+1)) := by
    nlinarith [mul_le_mul_of_nonneg_left hf (by positivity : (0:ℝ)≤1+2002*C₁)]
  have hN:=D.toUnitWave.growth_nonneg ha₀ 0
  dsimp only [excursionCostConstant]
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤1+2002*C₁) hF) hN]

end SharpNodal.Profiles

noncomputable section
open scoped BigOperators
open Set
namespace SharpNodal.Grid

lemma mem_atLevel {A : ℕ} (hA : 0<A) (n : ℕ) (x : Point) : x∈(atLevel A n x).points A := by
  apply (mem_square_div (pow_pos hA n)).mpr
  intro i
  simp only [atLevel,Nat.cast_pow]

lemma eq_atLevel {A : ℕ} (hA : 0<A) {Q : Cell} {x : Point} (hx : x∈Q.points A) :
    Q=atLevel A Q.level x := Cell.equal_level_eq_of_intersection hA rfl hx (mem_atLevel hA _ _)

lemma mem_fullTree {A : ℕ} (hA : 0<A) {Q root : Cell} :
    Q∈fullTree A root ↔ Q.level ≤ root.level ∧ Q.points A⊆root.points A := by
  classical
  constructor
  · intro h
    obtain ⟨n,hn,hQ⟩:=Finset.mem_biUnion.mp h
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hQ
    exact ⟨by simpa only [atLevel,Finset.mem_range,Nat.lt_succ_iff] using hn,
      Cell.subset_of_intersection hA (by simpa only [atLevel,Finset.mem_range,Nat.lt_succ_iff] using hn)
        (mem_atLevel hA n x) hx⟩
  · rintro ⟨hlev,hsub⟩
    obtain ⟨x,hx⟩:=(Finset.card_pos.mp (by rw [Cell.card_points]; exact pow_pos (Q.side_pos hA) 2))
    apply Finset.mem_biUnion.mpr
    refine ⟨Q.level,Finset.mem_range.mpr (by omega),Finset.mem_image.mpr ⟨x,hsub hx,?_⟩⟩
    exact (eq_atLevel hA hx).symm

lemma atLevel_mem_fullTree {A : ℕ} (hA : 0<A) {root : Cell} {x : Point}
    (hx : x∈root.points A) {n : ℕ} (hn : n ≤ root.level) : atLevel A n x∈fullTree A root := by
  apply (mem_fullTree hA).mpr
  exact ⟨hn,Cell.subset_of_intersection hA hn (mem_atLevel hA n x) hx⟩

lemma entries_subset (A : ℕ) (F : Finset Cell) (N : Cell → ℝ) (L H : ℝ) :
    entries A F N L H⊆F := Finset.filter_subset _ _

lemma entry_high {A : ℕ} {F : Finset Cell} {N : Cell → ℝ} {L H : ℝ} {Q : Cell}
    (hQ : Q∈entries A F N L H) : H<N Q := (Finset.mem_filter.mp hQ).2.1

lemma entry_separation {A : ℕ} {F : Finset Cell} {N : Cell → ℝ} {L H : ℝ} {Q P : Cell}
    (hQ : Q∈entries A F N L H) (hP : P∈entries A F N L H)
    (hlev : Q.level<P.level) (hsub : Q.points A⊆P.points A) :
    ∃R∈F,Q.level<R.level ∧ R.level<P.level ∧ Q.points A⊆R.points A ∧ N R≤L :=
  (Finset.mem_filter.mp hQ).2.2 P
    (Finset.mem_filter.mpr ⟨entries_subset A F N L H hP,hlev,hsub⟩) (entry_high hP)

lemma entry_parent_low {A : ℕ} {F : Finset Cell} {N : Cell → ℝ} {L H : ℝ} {Q P : Cell}
    (hQ : Q∈entries A F N L H) (hP : P∈F) (hlev : P.level=Q.level+1)
    (hsub : Q.points A⊆P.points A) : N P≤H := by
  by_contra hh
  have hp : H<N P := lt_of_not_ge hh
  obtain ⟨R,hR,hQR,hRP,-,-⟩:=(Finset.mem_filter.mp hQ).2.2 P
    (Finset.mem_filter.mpr ⟨hP,by omega,hsub⟩) hp
  omega

lemma entries_on_high_suffix {A : ℕ} (hA : 0<A) (F : Finset Cell) (N : Cell → ℝ)
    (L H : ℝ) (n : ℕ) (x : Point)
    (hhigh : ∀R∈F,R.level≤n → x∈R.points A → L<N R) :
    ((entries A F N L H).filter (fun Q =>Q.level≤n ∧ x∈Q.points A)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro Q hQ P hP
  rcases Finset.mem_filter.mp hQ with ⟨hQ,hQn,hxQ⟩
  rcases Finset.mem_filter.mp hP with ⟨hP,hPn,hxP⟩
  rcases lt_trichotomy Q.level P.level with h|h|h
  · obtain ⟨R,hR,hQR,hRP,hsub,hlow⟩:=entry_separation hQ hP h
      (Cell.subset_of_intersection hA h.le hxQ hxP)
    exact (not_lt_of_ge hlow (hhigh R hR (hRP.le.trans hPn) (hsub hxQ))).elim
  · exact Cell.equal_level_eq_of_intersection hA h hxQ hxP
  · obtain ⟨R,hR,hPR,hRQ,hsub,hlow⟩:=entry_separation hP hQ h
      (Cell.subset_of_intersection hA h.le hxP hxQ)
    exact (not_lt_of_ge hlow (hhigh R hR (hRQ.le.trans hQn) (hsub hxP))).elim

lemma smaller_entries_high_suffix {A : ℕ} (hA : 0<A) (F : Finset Cell) (N : Cell → ℝ)
    (L H : ℝ) (Q : Cell) (n : ℕ) (x : Point)
    (hhigh : ∀R∈F,R.level≤n → x∈R.points A → L<N R) :
    (Q.smallerAt A (entries A F N L H) x).card≤Q.level-n+1 := by
  classical
  let S:=Q.smallerAt A (entries A F N L H) x
  let Lo:=S.filter (fun P =>P.level≤n)
  let Hi:=S.filter (fun P =>¬P.level≤n)
  have hsplit : Lo.card+Hi.card=S.card := Finset.card_filter_add_card_filter_not _
  have hlo : Lo.card≤1 := by
    apply (Finset.card_le_card ?_).trans (entries_on_high_suffix hA F N L H n x hhigh)
    intro P hP
    rcases Finset.mem_filter.mp hP with ⟨hP,hn⟩
    rcases Finset.mem_filter.mp hP with ⟨hP,hPlev,hx⟩
    exact Finset.mem_filter.mpr ⟨hP,hn,hx⟩
  have hmap : MapsTo Cell.level (Hi : Set Cell) (Finset.Ico (n+1) Q.level) := by
    intro P hP
    rcases Finset.mem_filter.mp hP with ⟨hP,hn⟩
    have hlev := (Finset.mem_filter.mp hP).2.1
    exact Finset.mem_Ico.mpr ⟨by omega,hlev⟩
  have hinj : InjOn Cell.level (Hi : Set Cell) := by
    intro P hP R hR he
    exact Cell.equal_level_eq_of_intersection hA he
      (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).2.2
  have hhi:=Finset.card_le_card_of_injOn Cell.level hmap hinj
  rw [Nat.card_Ico] at hhi
  change S.card≤_
  omega

lemma terminal_has_active_entry {A : ℕ} (hA : 0<A) (root : Cell) (N : Cell → ℝ)
    {L H : ℝ} (hLH : L≤H) {x : Point} (hx : x∈root.points A)
    (ht : H<N (atLevel A 0 x)) :
    ∃Q∈entries A (fullTree A root) N L H,x∈activeSet A (fullTree A root) N L Q := by
  classical
  let F:=fullTree A root
  let G:=F.filter (fun Q =>x∈Q.points A ∧ H<N Q ∧
    ∀R∈F,R.level≤Q.level → x∈R.points A → L<N R)
  have hterm : atLevel A 0 x∈G := by
    refine Finset.mem_filter.mpr ⟨atLevel_mem_fullTree hA hx (Nat.zero_le _),mem_atLevel hA 0 x,ht,?_⟩
    intro R hR hn hRx
    have he : R=atLevel A 0 x := Cell.equal_level_eq_of_intersection hA (Nat.eq_zero_of_le_zero hn) hRx (mem_atLevel hA 0 x)
    rw [he]
    exact hLH.trans_lt ht
  obtain ⟨Q,hQ,hmax⟩:=Finset.exists_max_image G Cell.level ⟨_,hterm⟩
  rcases Finset.mem_filter.mp hQ with ⟨hQF,hxQ,hNQ,hhigh⟩
  refine ⟨Q,Finset.mem_filter.mpr ⟨hQF,hNQ,?_⟩,Finset.mem_filter.mpr ⟨hxQ,hhigh⟩⟩
  intro P hP hNP
  rcases Finset.mem_filter.mp hP with ⟨hPF,hQP,hsub⟩
  by_contra hbar
  have hPgood : ∀R∈F,R.level≤P.level → x∈R.points A → L<N R := by
    intro R hR hRP hxR
    by_cases hRQ : R.level≤Q.level
    · exact hhigh R hR hRQ hxR
    · by_cases he : R.level=P.level
      · have hEq:=Cell.equal_level_eq_of_intersection hA he hxR (hsub hxQ)
        rw [hEq]
        exact hLH.trans_lt hNP
      · by_contra hlow
        exact hbar ⟨R,hR,by omega,by omega,
          Cell.subset_of_intersection hA (by omega) hxQ hxR,le_of_not_gt hlow⟩
  have hPG : P∈G := Finset.mem_filter.mpr ⟨hPF,hsub hxQ,hNP,hPgood⟩
  have hh:=hmax P hPG
  omega

end SharpNodal.Grid

namespace SharpNodal.Grid

theorem terminal_sum_le {A : ℕ} (hA : 0<A) (root : Cell) (N : Cell → ℝ) {L H C : ℝ}
    (hLH : L≤H) (hH : 0≤H)
    (hN : ∀x∈root.points A,0≤N (atLevel A 0 x))
    (hlocal : ∀Q∈entries A (fullTree A root) N L H,
      (∑x∈activeSet A (fullTree A root) N L Q,N (atLevel A 0 x))≤C*(Q.points A).card) :
    (∑x∈root.points A,N (atLevel A 0 x))≤
      H*(root.points A).card+C*∑Q∈entries A (fullTree A root) N L H,((Q.points A).card:ℝ) := by
  classical
  let E:=entries A (fullTree A root) N L H
  let Ω:=activeSet A (fullTree A root) N L
  let t:=fun x =>N (atLevel A 0 x)
  have hΩ : ∀Q∈E,Ω Q⊆root.points A := by
    intro Q hQ
    exact (Finset.filter_subset _ _).trans ((mem_fullTree hA).mp (entries_subset _ _ _ _ _ hQ)).2
  have hp (x : Point) (hx : x∈root.points A) : t x≤H+∑Q∈E,if x∈Ω Q then t x else 0 := by
    have hnon : ∀ Q : Cell, 0 ≤ (if x∈Ω Q then t x else 0) := fun Q =>by split_ifs <;> first | exact hN x hx | rfl
    by_cases ht : t x≤H
    · exact ht.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun Q _ =>hnon Q)))
    · obtain ⟨Q,hQ,hxQ⟩:=terminal_has_active_entry hA root N hLH hx (lt_of_not_ge ht)
      have hsingle:=Finset.single_le_sum (s:=E) (fun P _ =>hnon P) hQ
      rw [ite_eq_left hxQ] at hsingle
      exact hsingle.trans (le_add_of_nonneg_left hH)
  have hsumQ (Q : Cell) (hQ : Q∈E) :
      (∑x∈root.points A,if x∈Ω Q then t x else 0)=∑x∈Ω Q,t x := by
    rw [←Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h =>h.2,fun h =>⟨hΩ Q hQ h,h⟩⟩
  calc
    _≤∑x∈root.points A,(H+∑Q∈E,if x∈Ω Q then t x else 0) := Finset.sum_le_sum (fun x hx =>hp x hx)
    _=H*(root.points A).card+∑Q∈E,∑x∈root.points A,if x∈Ω Q then t x else 0 := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]
    _=H*(root.points A).card+∑Q∈E,∑x∈Ω Q,t x := by
      congr 1
      exact Finset.sum_congr rfl (fun Q hQ =>hsumQ Q hQ)
    _≤H*(root.points A).card+∑Q∈E,C*(Q.points A).card :=
      add_le_add le_rfl (Finset.sum_le_sum (fun Q hQ =>hlocal Q hQ))
    _=_ := by rw [←Finset.mul_sum]

theorem terminal_mean_of_witnesses {A D c J : ℕ} (hA : 2≤A) (root : Cell)
    (N : Cell → ℝ) {L H C : ℝ} (hLH : L≤H) (hH : 0≤H) (hC : 0≤C)
    (hN : ∀x∈root.points A,0≤N (atLevel A 0 x))
    (hlocal : ∀Q∈entries A (fullTree A root) N L H,
      (∑x∈activeSet A (fullTree A root) N L Q,N (atLevel A 0 x))≤C*(Q.points A).card)
    (Y : Cell → Finset Point)
    (hnear : ∀Q∈entries A (fullTree A root) N L H,Y Q⊆Q.near A D)
    (hlower : ∀Q∈entries A (fullTree A root) N L H,(Q.points A).card ≤ c*(Y Q).card)
    (hsmall : ∀Q∈entries A (fullTree A root) N L H,∀x∈Y Q,
      (Q.smallerAt A (entries A (fullTree A root) N L H) x).card≤J) :
    (∑x∈root.points A,N (atLevel A 0 x))≤
      (H+C*packingConstant D c J)*(root.points A).card := by
  have hApos : 0<A := by omega
  have hp:=nearby_witness_packing hA (entries A (fullTree A root) N L H) root Y
    (fun Q hQ =>(mem_fullTree hApos).mp ((entries_subset A (fullTree A root) N L H) hQ))
    hnear hlower hsmall
  have hp' : (∑Q∈entries A (fullTree A root) N L H,((Q.points A).card:ℝ))≤
      (packingConstant D c J:ℝ)*(root.points A).card := by exact_mod_cast hp
  have hs:=terminal_sum_le hApos root N hLH hH hN hlocal
  nlinarith [mul_le_mul_of_nonneg_left hp' hC]

end SharpNodal.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQ4_Nl.NodalLength_TerminalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set

namespace SharpNodal.Grid
open Profiles

lemma wordPoint_mem (A n : ℕ) (p : Point) (w : GridWord A n) :
    wordPoint A n p w∈(Cell.mk n p).points A := by
  apply mem_square.mpr
  intro j
  have hl : (0:ℤ)≤(wordIndex A n w j:ℕ) := Int.natCast_nonneg _
  have hu : ((wordIndex A n w j:ℕ):ℤ)<(A:ℤ)^n := by exact_mod_cast (wordIndex A n w j).isLt
  dsimp only [wordPoint,Cell.side]
  push_cast
  constructor <;> nlinarith

lemma wordPoint_injective (A n : ℕ) (p : Point) : Function.Injective (wordPoint A n p) := by
  intro w v h
  apply wordIndex_injective A n
  funext j
  apply Fin.ext
  have hh:=congrFun h j
  dsimp only [wordPoint] at hh
  exact_mod_cast (add_left_cancel hh)

lemma image_wordPoint (A n : ℕ) (p : Point) :
    Finset.univ.image (wordPoint A n p)=(Cell.mk n p).points A := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨w,-,rfl⟩:=Finset.mem_image.mp hx
    exact wordPoint_mem A n p w
  · rw [Finset.card_image_iff.mpr (wordPoint_injective A n p).injOn,Finset.card_univ,
      gridWord_card,Cell.card_points]
    rfl

lemma sum_wordPoint (A n : ℕ) (p : Point) (f : Point → ℝ) :
    (∑w : GridWord A n,f (wordPoint A n p w))=∑x∈(Cell.mk n p).points A,f x := by
  rw [←image_wordPoint,Finset.sum_image (fun w _ v _ h =>wordPoint_injective A n p h)]

lemma wordPoint_zero (A : ℕ) (p : Point) (w : GridWord A 0) : wordPoint A 0 p w=p := by
  ext j
  simp [wordPoint,wordIndex]

lemma wordPoint_succ (A n : ℕ) (p : Point) (w : GridWord A (n+1)) :
    wordPoint A (n+1) p w=wordPoint A n (childPos A p (w 0)) (Fin.tail w) := by
  ext j
  simp only [wordPoint,wordIndex,childPos,Fin.val_cast,finProdFinEquiv,Equiv.coe_fn_mk,
    Int.natCast_add,Int.natCast_mul,Int.natCast_pow,pow_succ]
  ring

lemma cellScale_succ {A : ℕ} (hA : 0<A) (t : ℝ) (n : ℕ) (p q : Point) :
    cellScale A t (Cell.mk n q)=cellScale A t (Cell.mk (n+1) p)/(A:ℝ) := by
  have hAr : (A:ℝ)≠0 := by exact_mod_cast hA.ne'
  simp only [cellScale,pow_succ]
  field_simp

lemma cellMap_child {A : ℕ} (hA : 0<A) (t : ℝ) (n : ℕ) (p : Point) (i : GridIndex A) :
    cellMap A t (Cell.mk n (childPos A p i))=
      cellMap A t (Cell.mk (n+1) p) ∘ rescaleMap (gridCenter A i) (A:ℝ)⁻¹ := by
  have hAr : (A:ℝ)≠0 := by exact_mod_cast hA.ne'
  funext x
  ext j
  simp only [cellMap,cellScale,childPos,rescaleMap,extendedGridCenter,gridCenter,
    Function.comp_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    Int.cast_add,Int.cast_mul,Int.cast_natCast,pow_succ]
  field_simp
  ring

lemma pathGrowth_grid {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K : ℝ)
    (n : ℕ) (p : Point) (w : GridWord A n) :
    pathGrowth A n (U ∘ cellMap A t ⟨n,p⟩) (K*cellScale A t ⟨n,p⟩) w=
      gridGrowth A t U K (atLevel A 0 (wordPoint A n p w)) := by
  induction n generalizing p with
  | zero =>
    rw [wordPoint_zero]
    simp only [pathGrowth,gridGrowth,atLevel,pow_zero,Int.ediv_one]
  | succ n ih =>
    rw [pathGrowth,wordPoint_succ,←ih]
    rw [cellMap_child hA,cellScale_succ hA t n p]
    simp only [Function.comp_assoc,mul_div_assoc]

lemma pathHigh_grid {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K L : ℝ)
    (n : ℕ) (p : Point) (w : GridWord A n) :
    PathHigh A L n (U ∘ cellMap A t ⟨n,p⟩) (K*cellScale A t ⟨n,p⟩) w ↔
      ∀R : Cell,R.level≤n → wordPoint A n p w∈R.points A → L<gridGrowth A t U K R := by
  induction n generalizing p with
  | zero =>
    simp only [PathHigh]
    constructor
    · intro h R hR hx
      have he : R=⟨0,p⟩:=Cell.equal_level_eq_of_intersection hA (by change R.level=0; omega) hx (wordPoint_mem A 0 p w)
      simpa only [he,gridGrowth] using h
    · intro hh
      exact hh ⟨0,p⟩ le_rfl (wordPoint_mem A 0 p w)
  | succ n ih =>
    have heU : (U ∘ cellMap A t ⟨n,childPos A p (w 0)⟩)=
        (U ∘ cellMap A t ⟨n+1,p⟩) ∘ rescaleMap (gridCenter A (w 0)) (A:ℝ)⁻¹ := by
      rw [cellMap_child hA]; rfl
    have heK : K*cellScale A t ⟨n,childPos A p (w 0)⟩=(K*cellScale A t ⟨n+1,p⟩)/(A:ℝ) := by
      rw [cellScale_succ hA t n p]; ring
    rw [PathHigh,←heU,←heK,ih]
    constructor
    · rintro ⟨h,hh⟩ R hR hx
      by_cases he : R.level=n+1
      · have hEq : R=⟨n+1,p⟩:=Cell.equal_level_eq_of_intersection hA he hx (wordPoint_mem A (n+1) p w)
        simpa only [hEq,gridGrowth] using h
      · apply hh R (by omega)
        simpa only [←wordPoint_succ] using hx
    · intro hh
      exact ⟨hh ⟨n+1,p⟩ le_rfl (wordPoint_mem A (n+1) p w),
        fun R hR hx =>hh R (by omega) (by simpa only [wordPoint_succ] using hx)⟩

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

lemma pathHigh_activeSet {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K L : ℝ)
    {root Q : Cell} (hQ : Q∈fullTree A root) (w : GridWord A Q.level) :
    PathHigh A L Q.level (U ∘ cellMap A t Q) (K*cellScale A t Q) w ↔
      wordPoint A Q.level Q.pos w∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q := by
  rw [pathHigh_grid hA]
  constructor
  · intro h
    exact Finset.mem_filter.mpr ⟨wordPoint_mem A Q.level Q.pos w,fun R _ =>h R⟩
  · intro h R hR hx
    rcases Finset.mem_filter.mp h with ⟨hxQ,hhigh⟩
    have hxroot:=((mem_fullTree hA).mp hQ).2 hxQ
    have hRF : R∈fullTree A root := (mem_fullTree hA).mpr ⟨hR.trans ((mem_fullTree hA).mp hQ).1,
      Cell.subset_of_intersection hA (hR.trans ((mem_fullTree hA).mp hQ).1) hx hxroot⟩
    exact hhigh R hRF hR hx

lemma activeGrowth_sum {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K L : ℝ)
    {root Q : Cell} (hQ : Q∈fullTree A root) :
    (∑w : GridWord A Q.level,activeGrowth A L Q.level (U ∘ cellMap A t Q) (K*cellScale A t Q) w)=
      ∑x∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q,
        gridGrowth A t U K (atLevel A 0 x) := by
  have he (w : GridWord A Q.level) :
      activeGrowth A L Q.level (U ∘ cellMap A t Q) (K*cellScale A t Q) w=
        if wordPoint A Q.level Q.pos w∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q
        then gridGrowth A t U K (atLevel A 0 (wordPoint A Q.level Q.pos w)) else 0 := by
    rw [activeGrowth,pathGrowth_grid hA,pathHigh_activeSet hA t U K L hQ]
    split_ifs <;> rfl
  simp_rw [he]
  rw [sum_wordPoint A Q.level Q.pos (fun x => if x∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q
    then gridGrowth A t U K (atLevel A 0 x) else 0),←Finset.sum_filter]
  congr 1
  ext x
  simp only [activeSet,Finset.mem_filter,and_self_left]

theorem active_grid_sum {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (t : ℝ) (U : Plane → ℝ) (K : ℝ)
    {root Q : Cell} (hQ : Q∈fullTree A root) (E : ScaledWave Cp a₀)
    (hU : E.U=U ∘ cellMap A t Q) (hK : E.K=K*cellScale A t Q)
    (hbottom : a₀≤K*t) :
    (∑x∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q,
      gridGrowth A t U K (atLevel A 0 x))≤
      excursionCostConstant C₀ C₁ a₀*(gridGrowth A t U K Q+1)*(Q.points A).card := by
  have hAr : 0<(A:ℝ) := by exact_mod_cast (show 0<A by omega)
  have hbot : a₀≤E.K/(A:ℝ)^Q.level := by
    rw [hK,cellScale]
    have he : K*(t*(A:ℝ)^Q.level)/(A:ℝ)^Q.level=K*t := by field_simp
    rw [he]
    exact hbottom
  have hbound:=active_terminal_average hA ha₀ hC₀ hC₁ hrule Q.level E hbot
  rw [UnitWave.growth_zero,hU,hK,Fintype.expect_eq_sum_div_card,activeGrowth_sum (by omega) t U K L hQ] at hbound
  have hc : (0:ℝ)<Fintype.card (GridWord A Q.level) := by rw [gridWord_card]; positivity
  have hm:=(div_le_iff₀ hc).mp hbound
  simpa only [gridWord_card,Cell.card_points,Cell.side,gridGrowth] using hm

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

lemma childPos_parent {A : ℕ} (hA : 0<A) (Q : Cell) :
    childPos A (Q.parent A).pos (cellDigit hA Q)=Q.pos := by
  funext j
  have hAz : (A:ℤ)≠0 := by exact_mod_cast hA.ne'
  simp only [childPos,Cell.parent,cellDigit,Int.toNat_of_nonneg (Int.emod_nonneg _ hAz)]
  exact Int.ediv_mul_add_emod _ _

lemma cellMap_parent {A : ℕ} (hA : 0<A) (t : ℝ) (Q : Cell) :
    cellMap A t Q=cellMap A t (Q.parent A) ∘ rescaleMap (gridCenter A (cellDigit hA Q)) (A:ℝ)⁻¹ := by
  have hh:=cellMap_child hA t Q.level (Q.parent A).pos (cellDigit hA Q)
  rw [childPos_parent hA] at hh
  exact hh

lemma cellScale_parent {A : ℕ} (hA : 0<A) (t : ℝ) (Q : Cell) :
    cellScale A t Q=cellScale A t (Q.parent A)/(A:ℝ) :=
  cellScale_succ hA t Q.level (Q.parent A).pos Q.pos

lemma Cell.subset_parent {A : ℕ} (hA : 0<A) (Q : Cell) : Q.points A⊆(Q.parent A).points A := by
  intro x hx
  apply (mem_square_div ((Q.parent A).side_pos hA)).mpr
  intro j
  have hh:=Q.div_of_mem hA hx (show Q.level≤Q.level+1 by omega) j
  simpa only [Cell.side,Cell.parent,Nat.cast_pow,Nat.add_sub_cancel_left,pow_one] using hh

lemma Cell.parent_mem_fullTree {A : ℕ} (hA : 0<A) {root Q : Cell}
    (hQ : Q∈fullTree A root) (hn : Q.level < root.level) : Q.parent A∈fullTree A root := by
  obtain ⟨x,hx⟩:=Finset.card_pos.mp (by rw [Cell.card_points]; exact pow_pos (Q.side_pos hA) 2)
  exact (mem_fullTree hA).mpr ⟨by change Q.level+1 ≤ root.level; omega,
    Cell.subset_of_intersection hA (by change Q.level+1 ≤ root.level; omega)
      (Q.subset_parent hA hx) (((mem_fullTree hA).mp hQ).2 hx)⟩

lemma Cell.smallerAt_card_le {A : ℕ} (hA : 0<A) (F : Finset Cell) (Q : Cell) (x : Point) :
    (Q.smallerAt A F x).card≤Q.level := by
  have hm : MapsTo Cell.level (Q.smallerAt A F x : Set Cell) (Finset.range Q.level) := by
    intro R hR
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hR).2.1
  have hi : InjOn Cell.level (Q.smallerAt A F x : Set Cell) := by
    intro R hR S hS he
    exact Cell.equal_level_eq_of_intersection hA he (Finset.mem_filter.mp hR).2.2 (Finset.mem_filter.mp hS).2.2
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn Cell.level hm hi

theorem aligned_waves {A : ℕ} {Cp a₀ C₀ C₁ L : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hL : 0≤L) (hrule : DescentRule A Cp a₀ C₀ C₁ L)
    (t : ℝ) (U : Plane → ℝ) (K : ℝ) (root : Cell)
    (D : ScaledWave Cp a₀) (hDU : D.U=U ∘ cellMap A t root)
    (hDK : D.K=K*cellScale A t root) (hbottom : a₀≤K*t) :
    ∀Q∈fullTree A root,∃E : ScaledWave Cp a₀,
      E.U=U ∘ cellMap A t Q ∧ E.K=K*cellScale A t Q := by
  have hApos : 0<A := by omega
  have hAr : (1:ℝ)≤A := by exact_mod_cast (show 1≤A by omega)
  have hall : ∀d : ℕ,∀Q∈fullTree A root,root.level-Q.level=d →
      ∃E : ScaledWave Cp a₀,E.U=U ∘ cellMap A t Q ∧ E.K=K*cellScale A t Q := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hQ hd
      by_cases he : Q.level=root.level
      · obtain ⟨x,hx⟩:=Finset.card_pos.mp (by rw [Cell.card_points]; exact pow_pos (Q.side_pos hApos) 2)
        have hEq:=Cell.equal_level_eq_of_intersection hApos he hx (((mem_fullTree hApos).mp hQ).2 hx)
        subst Q
        exact ⟨D,hDU,hDK⟩
      · have hlt : Q.level < root.level := by have := ((mem_fullTree hApos).mp hQ).1; omega
        have hP:=(Cell.parent_mem_fullTree hApos hQ hlt)
        obtain ⟨E,hEU,hEK⟩:=ih (root.level-(Q.parent A).level) (by dsimp only [Cell.parent]; omega)
          (Q.parent A) hP rfl
        have hnext : a₀≤E.K/(A:ℝ) := by
          rw [hEK,mul_div_assoc,←cellScale_parent hApos t Q,cellScale,←mul_assoc]
          exact hbottom.trans (le_mul_of_one_le_right (ha₀.le.trans hbottom) (one_le_pow₀ hAr))
        let b : Plane := (L+1) • EuclideanSpace.single 0 1
        have hb : L<‖b‖ := by simp [b,norm_smul,abs_of_pos (by linarith : 0<L+1)]
        obtain ⟨Es,b',hc,-,-⟩:=hrule E b hnext (Or.inr hb)
        refine ⟨Es (cellDigit hApos Q),?_,?_⟩
        · rw [(hc _).2.1,hEU,cellMap_parent hApos t Q]
          rfl
        · rw [(hc _).2.2.1,hEK,cellScale_parent hApos t Q]
          ring
  intro Q hQ
  exact hall (root.level-Q.level) Q hQ rfl

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

lemma cellScale_offset {A : ℕ} (hA : 0<A) (t : ℝ) (n m : ℕ) (p q : Point) :
    cellScale A t ⟨n,offsetPos A m p q⟩=cellScale A t ⟨n+m,p⟩*((A:ℝ)⁻¹)^m := by
  have hAr : (A:ℝ)≠0 := by exact_mod_cast hA.ne'
  simp only [cellScale,pow_add,inv_pow]
  field_simp

lemma cellMap_offset {A : ℕ} (hA : 0<A) (t : ℝ) (n m : ℕ) (p q : Point) :
    cellMap A t ⟨n,offsetPos A m p q⟩=cellMap A t ⟨n+m,p⟩ ∘
      rescaleMap (extendedGridCenter (((A:ℝ)⁻¹)^m) q) (((A:ℝ)⁻¹)^m) := by
  have hAr : (A:ℝ)≠0 := by exact_mod_cast hA.ne'
  funext x
  ext j
  simp only [cellMap,cellScale,offsetPos,rescaleMap,extendedGridCenter,
    Function.comp_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,
    Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast,pow_add,inv_pow]
  field_simp
  ring

lemma offset_points_near {A : ℕ} (hA : 1≤A) (n m : ℕ) (p q : Point)
    (hy : ‖extendedGridCenter (((A:ℝ)⁻¹)^m) q‖+2000*((A:ℝ)⁻¹)^m<3) :
    (Cell.mk n (offsetPos A m p q)).points A⊆(Cell.mk (n+m) p).near A 4 := by
  have hAr : (1:ℝ)≤A := by exact_mod_cast hA
  have hArpos : (0:ℝ)<A := by linarith
  have hB : (1:ℝ)≤(A:ℝ)^m := one_le_pow₀ hAr
  have hBpos : (0:ℝ)<(A:ℝ)^m := by positivity
  have hrpos : (0:ℝ)<((A:ℝ)⁻¹)^m := by positivity
  have hq (j : Fin 2) : -4*(A:ℤ)^m≤q j ∧ q j+1≤5*(A:ℤ)^m := by
    have hc0 : |extendedGridCenter (((A:ℝ)⁻¹)^m) q j|≤‖extendedGridCenter (((A:ℝ)⁻¹)^m) q‖ :=
      plane_component_norm_le _ j
    have hc : |extendedGridCenter (((A:ℝ)⁻¹)^m) q j|<3 := hc0.trans_lt (by linarith)
    have hl:=mul_lt_mul_of_pos_right (abs_lt.mp hc).1 hBpos
    have hu:=mul_lt_mul_of_pos_right (abs_lt.mp hc).2 hBpos
    have he : extendedGridCenter (((A:ℝ)⁻¹)^m) q j*(A:ℝ)^m=
        -(A:ℝ)^m/2+(q j:ℝ)+1/2 := by
      simp only [extendedGridCenter,inv_pow]
      field_simp
      ring
    rw [he] at hl hu
    have hh : -4*(A:ℝ)^m≤(q j:ℝ) ∧ (q j:ℝ)+1≤5*(A:ℝ)^m := by constructor <;> linarith
    exact_mod_cast hh
  intro x hx
  apply mem_neighborhood.mpr
  intro j
  have hx':=mem_square.mp hx j
  have hlow:=mul_le_mul_of_nonneg_right (hq j).1 (show (0:ℤ)≤(A:ℤ)^n by positivity)
  have hhigh:=mul_le_mul_of_nonneg_right (hq j).2 (show (0:ℤ)≤(A:ℤ)^n by positivity)
  dsimp only [Cell.side,offsetPos] at hx' ⊢
  push_cast at hx' ⊢
  rw [pow_add]
  constructor <;> nlinarith

lemma parent_near_in_child {A : ℕ} (hA : 0<A) (n : ℕ) (p : Point) (i : GridIndex A) :
    (Cell.mk (n+1) p).near A 4⊆(Cell.mk n (childPos A p i)).near A (5*A) := by
  intro x hx
  apply mem_neighborhood.mpr
  intro j
  have hx':=mem_neighborhood.mp hx j
  have hi0 : (0:ℤ)≤(i j:ℕ) := Int.natCast_nonneg _
  have hiA : ((i j:ℕ):ℤ)<A := by exact_mod_cast (i j).isLt
  have hAn : (0:ℤ)<(A:ℤ)^n := pow_pos (by exact_mod_cast hA) n
  dsimp only [Cell.side,childPos] at hx' ⊢
  push_cast at hx' ⊢
  rw [pow_succ] at hx'
  constructor <;> nlinarith

lemma Cell.parent_near {A : ℕ} (hA : 0<A) (Q : Cell) :
    (Q.parent A).near A 4⊆Q.near A (5*A) := by
  have hh:=parent_near_in_child hA Q.level (Q.parent A).pos (cellDigit hA Q)
  rw [childPos_parent hA] at hh
  exact hh

lemma side_card_comparison {A : ℕ} (hA : 1≤A) {Q P S : Cell} {m M : ℕ}
    (hQP : Q.level+1=P.level) (hPS : S.level+m=P.level) (hm : m≤M) :
    (Q.points A).card≤A^(2*M)*(S.points A).card := by
  simp only [Cell.card_points,Cell.side,←pow_mul,←pow_add]
  apply Nat.pow_le_pow_right hA
  omega

lemma fieldGrowth_rescale (U : Plane → ℝ) (K : ℝ) (y : Plane) {r : ℝ} (hr : 0 < r) :
    fieldGrowth (U ∘ rescaleMap y r) (K*r)=
      massExcess (centeredMass 0 U y (1000*r)) (centeredMass 0 U y r)/(K*r) := by
  have hh:=centered_excess_rescale (0:Plane) U y 0 hr 1000 1
  simpa only [smul_zero,rescaleMap,smul_zero,add_zero,mul_one,mul_comm,fieldGrowth] using congrArg (fun v : ℝ =>v/(K*r)) hh

lemma gridGrowth_child {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K : ℝ) (Q : Cell) :
    gridGrowth A t U K Q=
      massExcess (centeredMass 0 (U ∘ cellMap A t (Q.parent A)) (gridCenter A (cellDigit hA Q)) (1000*(A:ℝ)⁻¹))
        (centeredMass 0 (U ∘ cellMap A t (Q.parent A)) (gridCenter A (cellDigit hA Q)) (A:ℝ)⁻¹)/
        ((K*cellScale A t (Q.parent A))*(A:ℝ)⁻¹) := by
  have hAr : (0:ℝ)<A := by exact_mod_cast hA
  rw [gridGrowth,cellMap_parent hA t Q,cellScale_parent hA t Q]
  have he : U ∘ (cellMap A t (Q.parent A) ∘ rescaleMap (gridCenter A (cellDigit hA Q)) (A:ℝ)⁻¹)=
      (U ∘ cellMap A t (Q.parent A)) ∘ rescaleMap (gridCenter A (cellDigit hA Q)) (A:ℝ)⁻¹ := rfl
  rw [he,show K*(cellScale A t (Q.parent A)/(A:ℝ))=(K*cellScale A t (Q.parent A))*(A:ℝ)⁻¹ by ring]
  exact fieldGrowth_rescale _ _ _ (by positivity)

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

lemma goodWordPoints_subset (A n : ℕ) (p : Point) (P : GridWord A n → Prop) :
    goodWordPoints A n p P⊆(Cell.mk n p).points A := by
  intro x hx
  obtain ⟨w,-,rfl⟩:=Finset.mem_image.mp hx
  exact wordPoint_mem A n p w

lemma goodWordPoints_card {A : ℕ} (hA : 0<A) (n : ℕ) (p : Point) (P : GridWord A n → Prop)
    (hp : (3:ℝ)/4≤𝔼 w : GridWord A n,if P w then (1:ℝ) else 0) :
    ((Cell.mk n p).points A).card ≤ 2*(goodWordPoints A n p P).card := by
  have hc : (0:ℝ)<Fintype.card (GridWord A n) := by
    rw [gridWord_card]
    exact_mod_cast pow_pos (pow_pos hA n) 2
  have hs : (∑w : GridWord A n,if P w then (1:ℝ) else 0)=((Finset.univ.filter P).card:ℝ) := by
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [Fintype.expect_eq_sum_div_card,hs] at hp
  have hh:=(le_div_iff₀ hc).mp hp
  have hh' : (Fintype.card (GridWord A n):ℝ)≤2*((Finset.univ.filter P).card:ℝ) := by linarith
  have hhN : Fintype.card (GridWord A n)≤2*(Finset.univ.filter P).card := by exact_mod_cast hh'
  simpa only [goodWordPoints,Finset.card_image_iff.mpr (wordPoint_injective A n p).injOn,
    Cell.card_points,Cell.side,gridWord_card] using hhN

theorem entry_witness {A M : ℕ} {Cp a₀ L H : ℝ} (hA : 2≤A)
    (hpersist : ∀(D : UnitWave Cp a₀) (i : GridIndex A) (depth : ℕ),
      a₀≤D.K/(A:ℝ)^depth → D.growth 0≤H →
      H < massExcess (centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) →
      depth≤M ∨ PersistentSquare A L D depth M)
    (t : ℝ) (U : Plane → ℝ) (K : ℝ) (root : Cell) (hbottom : a₀≤K*t)
    (hroot : gridGrowth A t U K root≤H)
    (hW : ∀Q∈fullTree A root,∃E : ScaledWave Cp a₀,
      E.U=U ∘ cellMap A t Q ∧ E.K=K*cellScale A t Q)
    (Q : Cell) (hQ : Q∈entries A (fullTree A root) (gridGrowth A t U K) L H) :
    ∃Y : Finset Point,Y⊆Q.near A (5*A) ∧ (Q.points A).card≤(2*A^(2*M))*Y.card ∧
      ∀x∈Y,(Q.smallerAt A (entries A (fullTree A root) (gridGrowth A t U K) L H) x).card≤M+1 := by
  have hAp : 0<A := by omega
  have hAr : (0:ℝ)<A := by exact_mod_cast hAp
  have hQF:=entries_subset A (fullTree A root) (gridGrowth A t U K) L H hQ
  have hQhigh:=entry_high hQ
  have hlt : Q.level < root.level := by
    have hle:=((mem_fullTree hAp).mp hQF).1
    by_contra hbad
    have he : Q.level=root.level := by omega
    obtain ⟨x,hx⟩:=Finset.card_pos.mp (by rw [Cell.card_points]; exact pow_pos (Q.side_pos hAp) 2)
    have hEq:=Cell.equal_level_eq_of_intersection hAp he hx (((mem_fullTree hAp).mp hQF).2 hx)
    rw [hEq] at hQhigh
    linarith
  let P:=Q.parent A
  have hPF : P∈fullTree A root := Cell.parent_mem_fullTree hAp hQF hlt
  have hPlow : gridGrowth A t U K P≤H := entry_parent_low hQ hPF rfl (Q.subset_parent hAp)
  obtain ⟨D,hDU,hDK⟩:=hW P hPF
  have hbot : a₀≤D.K/(A:ℝ)^P.level := by
    rw [hDK,cellScale]
    have he : K*(t*(A:ℝ)^P.level)/(A:ℝ)^P.level=K*t := by field_simp
    rwa [he]
  have hDlow : D.growth 0≤H := by simpa only [UnitWave.growth_zero,hDU,hDK,gridGrowth] using hPlow
  have hDhigh : H < massExcess (centeredMass 0 D.U (gridCenter A (cellDigit hAp Q)) (1000*(A:ℝ)⁻¹))
      (centeredMass 0 D.U (gridCenter A (cellDigit hAp Q)) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) := by
    rw [hDU,hDK,←gridGrowth_child hAp t U K Q]
    exact hQhigh
  rcases hpersist D.toUnitWave (cellDigit hAp Q) P.level hbot hDlow hDhigh with hshallow|hp
  · refine ⟨Q.points A,square_subset_neighborhood _ _ _,?_,?_⟩
    · have hpow : 1≤A^(2*M) := one_le_pow₀ (by omega)
      nlinarith
    · intro x _
      exact (Q.smallerAt_card_le hAp _ x).trans (by dsimp only [P,Cell.parent] at hshallow; omega)
  · rcases hp with ⟨m,_hm2,hmM,hmd,p,hy,_hr,E,hEU,hEK,_hs,hprob⟩
    let n:=P.level-m
    let S : Cell:=⟨n,offsetPos A m P.pos p⟩
    have hP : (Cell.mk (n+m) P.pos)=P := Cell.ext (Nat.sub_add_cancel hmd) rfl
    have hmap : cellMap A t S=cellMap A t P ∘
        rescaleMap (extendedGridCenter (((A:ℝ)⁻¹)^m) p) (((A:ℝ)⁻¹)^m) := by
      have hh:=cellMap_offset hAp t n m P.pos p
      rwa [hP] at hh
    have hscale : cellScale A t S=cellScale A t P*((A:ℝ)⁻¹)^m := by
      have hh:=cellScale_offset hAp t n m P.pos p
      rwa [hP] at hh
    have hEUg : E.U=U ∘ cellMap A t S := by rw [hEU,hDU,hmap]; rfl
    have hEKg : E.K=K*cellScale A t S := by rw [hEK,hDK,hscale]; ring
    let Y:=goodWordPoints A n S.pos (HighWavePath A L n E)
    have hY : Y⊆S.points A := goodWordPoints_subset A n S.pos (HighWavePath A L n E)
    have hSc : (S.points A).card≤2*Y.card := goodWordPoints_card hAp n S.pos _ hprob
    have hcomp:=side_card_comparison (by omega : 1≤A) (Q:=Q) (P:=P) (S:=S) rfl
      (show S.level+m=P.level from Nat.sub_add_cancel hmd) hmM
    refine ⟨Y,?_,?_,?_⟩
    · have hh:=offset_points_near (by omega : 1≤A) n m P.pos p hy
      rw [hP] at hh
      exact hY.trans (hh.trans (Q.parent_near hAp))
    · calc
        (Q.points A).card≤A^(2*M)*(S.points A).card := hcomp
        _≤A^(2*M)*(2*Y.card) := Nat.mul_le_mul_left _ hSc
        _=(2*A^(2*M))*Y.card := by ring
    · intro x hx
      obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hx
      have hgood:=HighWavePath.raw (Finset.mem_filter.mp hw).2
      rw [hEUg,hEKg,pathHigh_grid hAp] at hgood
      have hh:=smaller_entries_high_suffix hAp (fullTree A root) (gridGrowth A t U K) L H Q n
        (wordPoint A n S.pos w) (fun R _ =>hgood R)
      exact hh.trans (by dsimp only [n,P,Cell.parent] at hmd ⊢; omega)

end SharpNodal.Grid

namespace SharpNodal.Grid
open Profiles

lemma gridChild_growth {A : ℕ} (hA : 0<A) (t : ℝ) (U : Plane → ℝ) (K : ℝ) (Q : Cell)
    {Cp a₀ : ℝ} (D E : ScaledWave Cp a₀)
    (hDU : D.U=U ∘ cellMap A t (Q.parent A)) (hDK : D.K=K*cellScale A t (Q.parent A))
    (hc : GridChild A D E (cellDigit hA Q)) : E.growth 0=gridGrowth A t U K Q := by
  have hEU : E.U=U ∘ cellMap A t Q := by rw [hc.2.1,hDU,cellMap_parent hA t Q]; rfl
  have hEK : E.K=K*cellScale A t Q := by rw [hc.2.2.1,hDK,cellScale_parent hA t Q]; ring
  simp only [UnitWave.growth_zero,hEU,hEK,gridGrowth]

lemma entryBound_nonneg (A : ℕ) {C₀ C₁ L a₀ H : ℝ}
    (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L) (ha₀ : 0<a₀) (hH : 0≤H) :
    0≤entryBound A C₀ C₁ L a₀ H := by dsimp [entryBound]; positivity

lemma entry_growth_grid {A : ℕ} {Cp a₀ C₀ C₁ L H : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L) (t : ℝ) (U : Plane → ℝ) (K : ℝ) (Q : Cell)
    (D : ScaledWave Cp a₀) (hDU : D.U=U ∘ cellMap A t (Q.parent A))
    (hDK : D.K=K*cellScale A t (Q.parent A))
    (hparent : gridGrowth A t U K (Q.parent A)≤H) (hbottom : a₀≤K*t) :
    gridGrowth A t U K Q≤entryBound A C₀ C₁ L a₀ H := by
  have hAp : 0<A := by omega
  have hAr : (1:ℝ)≤A := by exact_mod_cast (show 1≤A by omega)
  have hnext : a₀≤D.K/(A:ℝ) := by
    rw [hDK,mul_div_assoc,←cellScale_parent hAp t Q,cellScale,←mul_assoc]
    exact hbottom.trans (le_mul_of_one_le_right (ha₀.le.trans hbottom) (one_le_pow₀ hAr))
  let b : Plane:=(L+1) • EuclideanSpace.single 0 1
  have hb : L<‖b‖ := by simp [b,norm_smul,abs_of_pos (by linarith : 0<L+1)]
  obtain ⟨Es,b',hc,-,-⟩:=hrule D b hnext (Or.inr hb)
  have hlow : D.growth 0≤H := by simpa only [UnitWave.growth_zero,hDU,hDK,gridGrowth] using hparent
  have hh:=entry_growth_bound hA ha₀ hC₀ hC₁ hL hrule D hlow hnext (cellDigit hAp Q) (Es (cellDigit hAp Q)) (hc _)
  rw [gridChild_growth hAp t U K Q D (Es (cellDigit hAp Q)) hDU hDK (hc _)] at hh
  exact hh

lemma entry_level_lt {A : ℕ} (hA : 0<A) {root Q : Cell} {N : Cell → ℝ} {L H : ℝ}
    (hroot : N root≤H) (hQ : Q∈entries A (fullTree A root) N L H) : Q.level < root.level := by
  have hQF:=entries_subset A (fullTree A root) N L H hQ
  have hle:=((mem_fullTree hA).mp hQF).1
  by_contra hbad
  have he : Q.level=root.level := by omega
  obtain ⟨x,hx⟩:=Finset.card_pos.mp (by rw [Cell.card_points]; exact pow_pos (Q.side_pos hA) 2)
  have hEq:=Cell.equal_level_eq_of_intersection hA he hx (((mem_fullTree hA).mp hQF).2 hx)
  have hh:=entry_high hQ
  rw [hEq] at hh
  linarith

theorem terminal_mean_grid {A M : ℕ} {Cp a₀ C₀ C₁ L H : ℝ} (hA : 2≤A)
    (ha₀ : 0<a₀) (hC₀ : 0≤C₀) (hC₁ : 0≤C₁) (hL : 0≤L) (hLH : L≤H)
    (hrule : DescentRule A Cp a₀ C₀ C₁ L)
    (hpersist : ∀(D : UnitWave Cp a₀) (i : GridIndex A) (depth : ℕ),
      a₀≤D.K/(A:ℝ)^depth → D.growth 0≤H →
      H < massExcess (centeredMass 0 D.U (gridCenter A i) (1000*(A:ℝ)⁻¹))
        (centeredMass 0 D.U (gridCenter A i) (A:ℝ)⁻¹)/(D.K*(A:ℝ)⁻¹) →
      depth≤M ∨ PersistentSquare A L D depth M)
    (t : ℝ) (U : Plane → ℝ) (K : ℝ) (root : Cell) (hbottom : a₀≤K*t)
    (hroot : gridGrowth A t U K root≤H)
    (hW : ∀Q∈fullTree A root,∃E : ScaledWave Cp a₀,
      E.U=U ∘ cellMap A t Q ∧ E.K=K*cellScale A t Q) :
    (∑x∈root.points A,gridGrowth A t U K (atLevel A 0 x))≤
      (H+excursionCostConstant C₀ C₁ a₀*(entryBound A C₀ C₁ L a₀ H+1)*
        packingConstant (5*A) (2*A^(2*M)) (M+1))*(root.points A).card := by
  have hAp : 0<A := by omega
  have hH : 0≤H := hL.trans hLH
  let C:=excursionCostConstant C₀ C₁ a₀*(entryBound A C₀ C₁ L a₀ H+1)
  have hcost:=excursionCostConstant_nonneg hC₀ hC₁ ha₀
  have hB:=entryBound_nonneg A hC₀ hC₁ hL ha₀ hH
  have hC : 0≤C := mul_nonneg hcost (by linarith)
  have hN : ∀x∈root.points A,0≤gridGrowth A t U K (atLevel A 0 x) := by
    intro x hx
    obtain ⟨E,hEU,hEK⟩:=hW (atLevel A 0 x) (atLevel_mem_fullTree hAp hx (Nat.zero_le _))
    have hh:=E.toUnitWave.growth_nonneg ha₀ 0
    simpa only [UnitWave.growth_zero,hEU,hEK,gridGrowth] using hh
  have hlocal : ∀Q∈entries A (fullTree A root) (gridGrowth A t U K) L H,
      (∑x∈activeSet A (fullTree A root) (gridGrowth A t U K) L Q,
        gridGrowth A t U K (atLevel A 0 x))≤C*(Q.points A).card := by
    intro Q hQ
    have hQF:=entries_subset A (fullTree A root) (gridGrowth A t U K) L H hQ
    obtain ⟨E,hEU,hEK⟩:=hW Q hQF
    have hPF:=Cell.parent_mem_fullTree hAp hQF (entry_level_lt hAp hroot hQ)
    obtain ⟨D,hDU,hDK⟩:=hW (Q.parent A) hPF
    have hPlow:=entry_parent_low hQ hPF rfl (Q.subset_parent hAp)
    have hentry:=entry_growth_grid hA ha₀ hC₀ hC₁ hL hrule t U K Q D hDU hDK hPlow hbottom
    have hs:=active_grid_sum hA ha₀ hC₀ hC₁ hrule t U K hQF E hEU hEK hbottom
    exact hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (add_le_add hentry le_rfl) hcost) (Nat.cast_nonneg _))
  have hwit : ∀Q : Cell,∃Y : Finset Point,Q∈entries A (fullTree A root) (gridGrowth A t U K) L H →
      Y⊆Q.near A (5*A) ∧ (Q.points A).card≤(2*A^(2*M))*Y.card ∧
        ∀x∈Y,(Q.smallerAt A (entries A (fullTree A root) (gridGrowth A t U K) L H) x).card≤M+1 := by
    intro Q
    by_cases hQ : Q∈entries A (fullTree A root) (gridGrowth A t U K) L H
    · obtain ⟨Y,hY⟩:=entry_witness hA hpersist t U K root hbottom hroot hW Q hQ
      exact ⟨Y,fun _ =>hY⟩
    · exact ⟨∅,fun h =>(hQ h).elim⟩
  choose Y hY using hwit
  exact terminal_mean_of_witnesses hA root (gridGrowth A t U K) hLH hH hC hN hlocal Y
    (fun Q hQ =>(hY Q hQ).1) (fun Q hQ =>(hY Q hQ).2.1) (fun Q hQ =>(hY Q hQ).2.2)

end SharpNodal.Grid

noncomputable section
open scoped BigOperators Classical
open Set
namespace SharpNodal.Grid
open Profiles

lemma cellScale_root {A : ℕ} (hA : 0<A) (n : ℕ) :
    cellScale A ((A:ℝ)^n)⁻¹ ⟨n,0⟩=1 := by
  have h : (A:ℝ)^n≠0 := pow_ne_zero _ (by exact_mod_cast hA.ne')
  exact inv_mul_cancel₀ h

lemma cellMap_root {A : ℕ} (hA : 0<A) (n : ℕ) :
    cellMap A ((A:ℝ)^n)⁻¹ ⟨n,0⟩=id := by
  funext x
  ext j
  norm_num [cellMap,cellScale_root hA n,rescaleMap,extendedGridCenter]

theorem uniform_terminal_growth_oai : ∃A : ℕ,10000<A ∧
    ∀Cp : ℝ,0≤Cp → ∀a₀ : ℝ,0<a₀ → ∀Cinit : ℝ,
    ∃C : ℝ,0≤C ∧ ∀(D : ScaledWave Cp a₀) (n : ℕ),
      D.growth 0≤Cinit → a₀≤D.K/(A:ℝ)^n →
      (𝔼 w : GridWord A n,pathGrowth A n D.U D.K w)≤C := by
  obtain ⟨A,hA,C₁,hC₁,hdescent⟩:=actual_descent_rule
  refine ⟨A,hA,?_⟩
  intro Cp hCp a₀ ha₀ Cinit
  obtain ⟨C₀,L,hC₀,hL,hdescent⟩:=hdescent Cp hCp
  have hC₀' : 0≤C₀ := by linarith
  have hrule:=hdescent a₀ ha₀
  obtain ⟨H,hH,M,hpersist⟩:=uniform_persistence_alternative hCp ha₀ hC₀' hC₁.le hL.le hA hrule (max Cinit L)
  have hCH : Cinit≤H := (le_max_left Cinit L).trans ((le_max_right 1 (max Cinit L)).trans hH.le)
  have hLH : L≤H := (le_max_right Cinit L).trans ((le_max_right 1 (max Cinit L)).trans hH.le)
  have hH0 : 0≤H := hL.le.trans hLH
  let C := H+excursionCostConstant C₀ C₁ a₀*(entryBound A C₀ C₁ L a₀ H+1)*
    packingConstant (5*A) (2*A^(2*M)) (M+1)
  have hcost:=excursionCostConstant_nonneg hC₀' hC₁.le ha₀
  have hB:=entryBound_nonneg A hC₀' hC₁.le hL.le ha₀ hH0
  have hpack : (0:ℝ)≤packingConstant (5*A) (2*A^(2*M)) (M+1) := by positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro D n hinit hbottom
  have hAp : 0<A := by omega
  let t : ℝ := ((A:ℝ)^n)⁻¹
  let root : Cell := ⟨n,0⟩
  have hscale : cellScale A t root=1 := cellScale_root hAp n
  have hmap : cellMap A t root=id := cellMap_root hAp n
  have hDU : D.U=D.U ∘ cellMap A t root := by rw [hmap]; rfl
  have hDK : D.K=D.K*cellScale A t root := by rw [hscale,mul_one]
  have hbottom' : a₀≤D.K*t := by simpa only [t,div_eq_mul_inv] using hbottom
  have hroot : gridGrowth A t D.U D.K root≤H := by
    simpa only [gridGrowth,←hDU,←hDK,←UnitWave.growth_zero] using hinit.trans hCH
  have hwaves:=aligned_waves (by omega : 2≤A) ha₀ hL.le hrule t D.U D.K root D hDU hDK hbottom'
  have hsum:=terminal_mean_grid (by omega : 2≤A) ha₀ hC₀' hC₁.le hL.le hLH hrule hpersist
    t D.U D.K root hbottom' hroot hwaves
  have hpath (w : GridWord A n) : pathGrowth A n D.U D.K w=
      gridGrowth A t D.U D.K (atLevel A 0 (wordPoint A n 0 w)) := by
    have hh:=pathGrowth_grid hAp t D.U D.K n 0 w
    rw [←hDU,←hDK] at hh
    exact hh
  rw [Fintype.expect_eq_sum_div_card]
  simp_rw [hpath]
  rw [sum_wordPoint A n 0 (fun x =>gridGrowth A t D.U D.K (atLevel A 0 x)),gridWord_card]
  have hcard : (0:ℝ)<((A^n)^2:ℕ) := by exact_mod_cast pow_pos (pow_pos hAp n) 2
  apply (div_le_iff₀ hcard).mpr
  simpa only [C,root,Cell.card_points,Cell.side] using hsum

end SharpNodal.Grid

end
end

end OAI
end

theorem solution : type_of% @OAI.SharpNodal.Grid.uniform_terminal_growth_oai := @OAI.SharpNodal.Grid.uniform_terminal_growth_oai
