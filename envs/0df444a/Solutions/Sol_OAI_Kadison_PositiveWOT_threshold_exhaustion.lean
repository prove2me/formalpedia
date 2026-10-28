-- Prove2me | solution 1 for OAI.Kadison.PositiveWOT.threshold_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:36.805306+00:00
-- url     : https://prove2.me/submissions/2d74a7eb-efb5-4bcf-91b0-55de2d176581

import Mathlib
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C040
import Definitions.Def_OAIQ039C041

section
-- module Solutions.OAIQ039_CM.Compat
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma abs_mul_initial (T : H →L[ℂ] H) : CFC.abs T*rightSupport T=CFC.abs T := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  simpa only [star_mul,hs,(isProjection_rightSupport T).isSelfAdjoint.star_eq] using
    congrArg star (initial_mul_abs T)

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PositiveCauchySchwarz
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_inner (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y)=inner ℂ (A x) y := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))
  have he := hs (CFC.sqrt A x) y
  have hh : CFC.sqrt A*CFC.sqrt A=A := by simpa only [pow_two] using CFC.sq_sqrt A ha
  change inner ℂ ((CFC.sqrt A*CFC.sqrt A) x) y=
    inner ℂ (CFC.sqrt A x) (CFC.sqrt A y) at he
  exact he.symm.trans (congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) hh)

lemma sqrt_norm_sq (A : H →L[ℂ] H) (ha : 0≤A) (x : H) :
    ‖CFC.sqrt A x‖^2=(inner ℂ (A x) x).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ),sqrt_inner A ha x x]
  rfl

lemma positive_cauchySchwarz (A : H →L[ℂ] H) (ha : 0≤A) (x y : H) :
    ‖inner ℂ (A x) y‖^2≤(inner ℂ (A x) x).re*(inner ℂ (A y) y).re := by
  have hh := norm_inner_le_norm (𝕜:=ℂ) (CFC.sqrt A x) (CFC.sqrt A y)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
  rw [mul_pow,sqrt_norm_sq A ha x,sqrt_norm_sq A ha y,sqrt_inner A ha x y] at hs
  exact hs

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PositiveWOT
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma inner_mono {A B : H →L[ℂ] H} (h : A≤B) (x : H) :
    (inner ℂ (A x) x).re≤(inner ℂ (B x) x).re := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr h)
  have hh : 0≤(inner ℂ ((B-A) x) x).re := hp.re_inner_nonneg_left x
  simpa only [sub_apply,inner_sub_left,Complex.sub_re,sub_nonneg] using hh

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralThreshold
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma positive_apply_eq_zero {A : H →L[ℂ] H} (ha : 0≤A) {x : H}
    (hx : (inner ℂ (A x) x).re=0) : A x=0 := by
  have hh := positive_cauchySchwarz A ha x (A x)
  rw [hx,zero_mul] at hh
  have hn : inner ℂ (A x) (A x)=0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (inner ℂ (A x) (A x))])
  exact (inner_self_eq_zero (𝕜:=ℂ)).mp hn

lemma rightSupport_mono {A B : H →L[ℂ] H} (hA : 0≤A) (hB : 0≤B) (hab : A≤B) :
    Polar.rightSupport A≤Polar.rightSupport B := by
  have hp := Polar.isProjection_rightSupport B
  have hfix : B*Polar.rightSupport B=B := by
    simpa only [CFC.abs_of_nonneg B hB] using Polar.abs_mul_initial B
  have he : B*(1-Polar.rightSupport B)=0 := by rw [mul_sub,mul_one,hfix,sub_self]
  have ha : A*(1-Polar.rightSupport B)=0 := by
    ext x
    change A ((1-Polar.rightSupport B) x)=0
    apply positive_apply_eq_zero hA
    have hh := inner_mono hab ((1-Polar.rightSupport B) x)
    have hz : B ((1-Polar.rightSupport B) x)=0 := congrArg (fun T : H →L[ℂ] H => T x) he
    rw [hz,inner_zero_left,Complex.zero_re] at hh
    exact le_antisymm hh (((ContinuousLinearMap.nonneg_iff_isPositive _).mp hA).re_inner_nonneg_left _)
  apply Polar.rightSupport_le A (Polar.rightSupport B) hp
  rw [mul_sub,mul_one,sub_eq_zero] at ha
  exact ha.symm

lemma cfc_shift_posPart (B : H →L[ℂ] H) (hB : IsSelfAdjoint B) (r : ℝ) :
    (B-r • (1:H →L[ℂ] H))⁺=cfc (fun t : ℝ => (t-r)⁺) B := by
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have he : cfc (fun t : ℝ => t-r) B=B-r • (1:H →L[ℂ] H) := by
    change cfc (fun t : ℝ => id t - (fun _ : ℝ => r) t) B = _
    rw [cfc_sub (id : ℝ → ℝ) (fun _ => r),cfc_id ℝ B hB,cfc_const r B hB]
    exact congrArg (B-·) (Algebra.algebraMap_eq_smul_one r)
  rw [←he]
  exact (cfc_comp (fun t : ℝ => t⁺) (fun t : ℝ => t-r) B).symm

lemma threshold_projection (B : H →L[ℂ] H) (r : ℝ) : IsStarProjection (threshold B r) :=
  Polar.isProjection_rightSupport _

lemma threshold_mem (M : VonNeumannAlgebra H) {B : H →L[ℂ] H} (hB : B∈M) (r : ℝ) :
    threshold B r∈M := by
  apply Polar.rightSupport_mem M
  apply Polar.posPart_mem M
  apply M.toStarSubalgebra.sub_mem hB
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (Complex.ofReal r) • (1:H →L[ℂ] H)∈M
  exact M.toStarSubalgebra.smul_mem M.one_mem _

lemma threshold_antitone {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) : Antitone (threshold B) := by
  intro r s hrs
  have hle : (B-s • (1:H →L[ℂ] H))⁺≤(B-r • (1:H →L[ℂ] H))⁺ := by
    rw [cfc_shift_posPart B hB,cfc_shift_posPart B hB]
    exact cfc_mono (R:=ℝ) (a:=B) (fun t _ => sup_le_sup (sub_le_sub_left hrs t) le_rfl)
      (Continuous.continuousOn ((continuous_id.sub continuous_const).max continuous_const))
      (Continuous.continuousOn ((continuous_id.sub continuous_const).max continuous_const))
  exact rightSupport_mono (CFC.posPart_nonneg (B-s • (1:H →L[ℂ] H)))
    (CFC.posPart_nonneg (B-r • (1:H →L[ℂ] H))) hle

lemma threshold_commute {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    Commute (threshold B r) B := by
  let a : H →L[ℂ] H := B-r • (1:H →L[ℂ] H)
  have hr : Commute (r • (1:H →L[ℂ] H)) B := (Commute.one_left B).smul_left r
  have hc : Commute a B := (Commute.refl B).sub_left hr
  have hp : Commute a⁺ B := hc.cfcₙ_real (·⁺)
  have hs : Commute a⁺ (star B) := by rwa [hB.star_eq]
  have hh : Commute (Polar.partialIsometry a⁺) B := Polar.partialIsometry_commutes a⁺ B hp hs
  rw [Polar.partialIsometry_of_nonneg (CFC.posPart_nonneg a)] at hh
  exact hh

lemma threshold_mul_shift {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    threshold B r*(B-r • (1:H →L[ℂ] H))=(B-r • (1:H →L[ℂ] H))⁺ := by
  let a := B-r • (1:H →L[ℂ] H)
  have ha : IsSelfAdjoint a := hB.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have hp : Polar.rightSupport a⁺*a⁺=a⁺ := by
    simpa only [CFC.abs_of_nonneg _ (CFC.posPart_nonneg a)] using Polar.initial_mul_abs a⁺
  have hn : Polar.rightSupport a⁺*a⁻=0 :=
    Polar.rightSupport_mul_eq_zero_of_nonneg (CFC.posPart_nonneg a) (CFC.posPart_mul_negPart a)
  change Polar.rightSupport a⁺*a=a⁺
  nth_rw 2 [←CFC.posPart_sub_negPart a ha]
  rw [mul_sub,hp,hn,sub_zero]

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralThresholdBounds
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_remainder {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    B*(1-threshold B r) ≤ r • (1-threshold B r) := by
  let a := B-r • (1:H →L[ℂ] H)
  have ha : IsSelfAdjoint a := hB.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have he : (1-threshold B r)*a= -a⁻ := by
    rw [sub_mul,one_mul,threshold_mul_shift hB r]
    change a-a⁺= -a⁻
    nth_rw 1 [←CFC.posPart_sub_negPart a ha]
    abel
  have hh : (1-threshold B r)*a≤0 := he ▸ neg_nonpos.mpr (CFC.negPart_nonneg a)
  dsimp only [a] at hh
  rw [mul_sub,mul_smul_comm,mul_one] at hh
  have hc : Commute (1-threshold B r) B := (Commute.one_left B).sub_left (threshold_commute hB r)
  rw [hc.eq] at hh
  exact sub_nonpos.mp hh

lemma threshold_remainder_nonneg {B : H →L[ℂ] H} (hB : 0≤B) (r : ℝ) :
    0≤B*(1-threshold B r) := by
  exact Commute.mul_nonneg hB (threshold_projection B r).one_sub.nonneg
    (((Commute.one_left B).sub_left (threshold_commute (IsSelfAdjoint.of_nonneg hB) r)).symm)

lemma threshold_remainder_norm {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0 ≤ r) :
    ‖B*(1-threshold B r)‖ ≤ r := by
  have hh := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (threshold_remainder (IsSelfAdjoint.of_nonneg hB) r) (threshold_remainder_nonneg hB r)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr] at hh
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left ((threshold_projection B r).one_sub.norm_le _) hr)

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralExhaustion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem threshold_exhaustion_oai (M : VonNeumannAlgebra H) {B : H →L[ℂ] H}
    (hBM : B∈M) (hB : 0≤B) (hi : Function.Injective B) :
    Monotone (fun n : ℕ => threshold B (1/((n:ℝ)+1))) ∧
      ∀ x,Tendsto (fun n : ℕ => threshold B (1/((n:ℝ)+1)) x) atTop (𝓝 x) := by
  let P (n : ℕ) := threshold B (1/((n:ℝ)+1))
  have hP (n : ℕ) : IsStarProjection (P n) := threshold_projection B _
  have hPM (n : ℕ) : P n∈M := threshold_mem M hBM _
  have hmono : Monotone P := by
    intro n m hnm
    apply threshold_antitone (IsSelfAdjoint.of_nonneg hB)
    apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(n:ℝ)+1)
    exact_mod_cast Nat.add_le_add_right hnm 1
  obtain ⟨W,hWM,hW,hPW,ht,hleast⟩ := ProjectionChains.exists_strong_sup M P hP hPM hmono
  have hnorm (n : ℕ) : ‖B*(1-W)‖≤1/((n:ℝ)+1) := by
    have he : P n*W=P n := ((hP n).le_iff_mul_eq_left hW).mp (hPW n)
    have hid : B*(1-W)=(B*(1-P n))*(1-W) := by noncomm_ring [he]
    rw [hid]
    calc
      _≤‖B*(1-P n)‖*‖1-W‖ := norm_mul_le _ _
      _≤(1/((n:ℝ)+1))*1 := mul_le_mul
        (threshold_remainder_norm hB (by positivity)) (hW.one_sub.norm_le _)
        (norm_nonneg _) (by positivity)
      _=1/((n:ℝ)+1) := mul_one _
  have hz : B*(1-W)=0 := norm_eq_zero.mp (le_antisymm
    (ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)) (Eventually.of_forall hnorm))
    (norm_nonneg _))
  have he : W=1 := by
    ext x
    have hh : B ((1-W) x)=B 0 := by
      rw [map_zero]
      exact congrArg (fun T : H →L[ℂ] H => T x) hz
    have hx := hi hh
    change x-W x=0 at hx
    exact (sub_eq_zero.mp hx).symm
  refine ⟨hmono,?_⟩
  intro x
  simpa only [he,one_apply_eq_self] using ht x

end Kadison.PositiveWOT

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PositiveWOT.threshold_exhaustion_oai.{u_1} := @OAI.Kadison.PositiveWOT.threshold_exhaustion_oai.{u_1}
