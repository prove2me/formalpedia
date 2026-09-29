-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage.covers_of_endpoint_enclosures
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:19:21.535854+00:00
-- url     : https://prove2.me/submissions/ec1a90e1-4de6-4502-bfec-432fa16e9c41

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_RB2_program_data

namespace GeneralCK.Certificates.E8TAxisReparamJet5
end GeneralCK.Certificates.E8TAxisReparamJet5
namespace GeneralCK.Certificates.E8InverseJet5Bridge
end GeneralCK.Certificates.E8InverseJet5Bridge
namespace GeneralCK.Certificates.E8TAxisReparamInterval
end GeneralCK.Certificates.E8TAxisReparamInterval
namespace GeneralCK.E8AnalyticGerm
end GeneralCK.E8AnalyticGerm

section
namespace GeneralCK.Certificates



namespace DyadicInterval



theorem scale_pos (p : ℕ) : 0 < scale p := by unfold scale; positivity
theorem scale_cast_pos (p : ℕ) : 0 < (scale p : ℝ) := by exact_mod_cast scale_pos p





















































end DyadicInterval
end GeneralCK.Certificates
end

section
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)













end GeneralCK
end

section
namespace GeneralCK.Certificates

structure Jet5 where
  d0 : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  d3 : ℝ → ℝ
  d4 : ℝ → ℝ
  d5 : ℝ → ℝ

namespace Jet5

def SoundAt (j : Jet5) (t : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 t) t ∧ HasDerivAt j.d1 (j.d2 t) t ∧
  HasDerivAt j.d2 (j.d3 t) t ∧ HasDerivAt j.d3 (j.d4 t) t ∧
  HasDerivAt j.d4 (j.d5 t) t



def const (c : ℝ) : Jet5 :=
  ⟨fun _ => c, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def variableJet : Jet5 :=
  ⟨id, fun _ => 1, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def add (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t + b.d0 t, fun t => a.d1 t + b.d1 t,
   fun t => a.d2 t + b.d2 t, fun t => a.d3 t + b.d3 t,
   fun t => a.d4 t + b.d4 t, fun t => a.d5 t + b.d5 t⟩

def neg (a : Jet5) : Jet5 :=
  ⟨fun t => -a.d0 t, fun t => -a.d1 t, fun t => -a.d2 t,
   fun t => -a.d3 t, fun t => -a.d4 t, fun t => -a.d5 t⟩

/-- Raw-derivative Leibniz propagation through order five. -/
def mul (a b : Jet5) : Jet5 :=
  ⟨fun t => a.d0 t * b.d0 t,
   fun t => a.d1 t * b.d0 t + a.d0 t * b.d1 t,
   fun t => a.d2 t * b.d0 t + 2*a.d1 t*b.d1 t + a.d0 t*b.d2 t,
   fun t => a.d3 t*b.d0 t + 3*a.d2 t*b.d1 t + 3*a.d1 t*b.d2 t + a.d0 t*b.d3 t,
   fun t => a.d4 t*b.d0 t + 4*a.d3 t*b.d1 t + 6*a.d2 t*b.d2 t +
     4*a.d1 t*b.d3 t + a.d0 t*b.d4 t,
   fun t => a.d5 t*b.d0 t + 5*a.d4 t*b.d1 t + 10*a.d3 t*b.d2 t +
     10*a.d2 t*b.d3 t + 5*a.d1 t*b.d4 t + a.d0 t*b.d5 t⟩



theorem soundAt_const (c t : ℝ) : (const c).SoundAt t := by
  exact ⟨hasDerivAt_const t c, hasDerivAt_const t 0, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem soundAt_variable (t : ℝ) : variableJet.SoundAt t := by
  exact ⟨hasDerivAt_id t, hasDerivAt_const t 1, hasDerivAt_const t 0,
    hasDerivAt_const t 0, hasDerivAt_const t 0⟩

theorem SoundAt.add {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.add b).SoundAt t := by
  exact ⟨ha.1.add hb.1, ha.2.1.add hb.2.1, ha.2.2.1.add hb.2.2.1,
    ha.2.2.2.1.add hb.2.2.2.1, ha.2.2.2.2.add hb.2.2.2.2⟩

theorem SoundAt.neg {a : Jet5} {t : ℝ} (ha : a.SoundAt t) : a.neg.SoundAt t := by
  exact ⟨ha.1.neg, ha.2.1.neg, ha.2.2.1.neg, ha.2.2.2.1.neg, ha.2.2.2.2.neg⟩

theorem SoundAt.mul {a b : Jet5} {t : ℝ} (ha : a.SoundAt t) (hb : b.SoundAt t) :
    (a.mul b).SoundAt t := by
  refine ⟨ha.1.mul hb.1, ?_, ?_, ?_, ?_⟩
  · convert! (ha.2.1.mul hb.1).add (ha.1.mul hb.2.1) using 1 <;>
      simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;> first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.1.mul hb.1).add
      ((ha.2.1.mul hb.2.1).const_mul 2)).add (ha.1.mul hb.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.1.mul hb.1).add
      ((ha.2.2.1.mul hb.2.1).const_mul 3)).add
      ((ha.2.1.mul hb.2.2.1).const_mul 3)).add (ha.1.mul hb.2.2.2.1)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((((ha.2.2.2.2.mul hb.1).add
      ((ha.2.2.2.1.mul hb.2.1).const_mul 4)).add
      ((ha.2.2.1.mul hb.2.2.1).const_mul 6)).add
      ((ha.2.1.mul hb.2.2.2.1).const_mul 4)).add (ha.1.mul hb.2.2.2.2)
    convert! h using 1 <;> simp only [Jet5.mul, Pi.add_apply, Pi.mul_apply] <;>
      first | (funext u; simp <;> ring) | ring

/-- The order-five jet of `exp (c+m*t)`.  This is the first transcendental
shape needed by the E8 parameterization (`c=0`, `m=-2`). -/
noncomputable def expAffine (c m : ℝ) : Jet5 :=
  ⟨fun t => Real.exp (c+m*t), fun t => Real.exp (c+m*t)*m,
   fun t => Real.exp (c+m*t)*m^2, fun t => Real.exp (c+m*t)*m^3,
   fun t => Real.exp (c+m*t)*m^4, fun t => Real.exp (c+m*t)*m^5⟩

theorem soundAt_expAffine (c m t : ℝ) : (expAffine c m).SoundAt t := by
  have hi : HasDerivAt (fun u : ℝ => c+m*u) m t := by
    convert! (hasDerivAt_const t c).add ((hasDerivAt_id t).mul_const m) using 1
    · funext u
      simp [id_eq, mul_comm]
    · ring
  have he := (Real.hasDerivAt_exp (c+m*t)).comp t hi
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! he using 1 <;> simp [expAffine]
  · convert! he.mul_const m using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^2) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^3) using 1 <;> simp [expAffine] <;> ring
  · convert! he.mul_const (m^4) using 1 <;> simp [expAffine] <;> ring




end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
namespace Jet5

/-- Raw derivatives of the reciprocal through order five. -/
noncomputable def inv (a : Jet5) : Jet5 :=
  ⟨a.d0⁻¹,
   -a.d1 / a.d0^2,
   (fun y => 2*(a.d1^2) y)/a.d0^3-a.d2/a.d0^2,
   (fun y => -6*(a.d1^3) y)/a.d0^4+
     ((fun y => 6*(a.d1*a.d2) y)/a.d0^3-a.d3/a.d0^2),
   (fun y => 24*(a.d1^4) y)/a.d0^5-(fun y => 36*(a.d1^2*a.d2) y)/a.d0^4+
     (fun y => 6*(a.d2^2) y)/a.d0^3+(fun y => 8*(a.d1*a.d3) y)/a.d0^3-
     a.d4/a.d0^2,
   fun t => -120*a.d1 t^5/a.d0 t^6+240*a.d1 t^3*a.d2 t/a.d0 t^5-
     90*a.d1 t*a.d2 t^2/a.d0 t^4-60*a.d1 t^2*a.d3 t/a.d0 t^4+
     20*a.d2 t*a.d3 t/a.d0 t^3+10*a.d1 t*a.d4 t/a.d0 t^3-
     a.d5 t/a.d0 t^2⟩

theorem SoundAt.inv {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.inv.SoundAt t := by
  have h2 : a.d0 t ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h3 : a.d0 t ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have h4 : a.d0 t ^ 4 ≠ 0 := pow_ne_zero 4 hn
  have h5 : a.d0 t ^ 5 ≠ 0 := pow_ne_zero 5 hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.inv hn using 1 <;> simp [Jet5.inv]
  · have h := ha.2.1.neg.div (ha.1.pow 2) h2
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 2).const_mul 2).div (ha.1.pow 3) h3).sub
      (ha.2.2.1.div (ha.1.pow 2) h2)
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h := (((ha.2.1.pow 3).const_mul (-6)).div (ha.1.pow 4) h4).add
      ((((ha.2.1.mul ha.2.2.1).const_mul 6).div (ha.1.pow 3) h3).sub
        (ha.2.2.2.1.div (ha.1.pow 2) h2))
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring
  · have h1 := ((ha.2.1.pow 4).const_mul 24).div (ha.1.pow 5) h5
    have h2term := (((ha.2.1.pow 2).mul ha.2.2.1).const_mul 36).div (ha.1.pow 4) h4
    have h3' := ((ha.2.2.1.pow 2).const_mul 6).div (ha.1.pow 3) h3
    have h4' := ((ha.2.1.mul ha.2.2.2.1).const_mul 8).div (ha.1.pow 3) h3
    have h5' := ha.2.2.2.2.div (ha.1.pow 2) h2
    have h := (((h1.sub h2term).add h3').add h4').sub h5'
    convert! h using 1 <;> simp only [Jet5.inv, Pi.neg_apply, Pi.pow_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply] <;>
      field_simp [hn] <;> ring

/-- Define logarithmic derivatives from `a' * a⁻¹`; this exposes the domain
hypothesis only in the soundness theorem. -/
noncomputable def log (a : Jet5) : Jet5 :=
  let r := a.inv
  ⟨fun t => Real.log (a.d0 t),
   fun t => a.d1 t*r.d0 t,
   fun t => a.d2 t*r.d0 t+a.d1 t*r.d1 t,
   fun t => a.d3 t*r.d0 t+2*a.d2 t*r.d1 t+a.d1 t*r.d2 t,
   fun t => a.d4 t*r.d0 t+3*a.d3 t*r.d1 t+3*a.d2 t*r.d2 t+a.d1 t*r.d3 t,
   fun t => a.d5 t*r.d0 t+4*a.d4 t*r.d1 t+6*a.d3 t*r.d2 t+
     4*a.d2 t*r.d3 t+a.d1 t*r.d4 t⟩

theorem SoundAt.log {a : Jet5} {t : ℝ} (ha : a.SoundAt t) (hn : a.d0 t ≠ 0) :
    a.log.SoundAt t := by
  have hr := ha.inv hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · convert! ha.1.log hn using 1 <;> simp [Jet5.log, Jet5.inv, div_eq_mul_inv]
  · convert! ha.2.1.mul hr.1 using 1 <;>
      simp [Jet5.log] <;> first | (funext u; simp <;> ring) | ring
  · have h := (ha.2.2.1.mul hr.1).add (ha.2.1.mul hr.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := ((ha.2.2.2.1.mul hr.1).add
      ((ha.2.2.1.mul hr.2.1).const_mul 2)).add
      (ha.2.1.mul hr.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring
  · have h := (((ha.2.2.2.2.mul hr.1).add
      ((ha.2.2.2.1.mul hr.2.1).const_mul 3)).add
      ((ha.2.2.1.mul hr.2.2.1).const_mul 3)).add
      (ha.2.1.mul hr.2.2.2.1)
    convert! h using 1 <;> simp [Jet5.log] <;>
      first | (funext u; simp <;> ring) | ring

end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology
























theorem biasB_pos {c : ℝ} (hc : 0 < c) (hc' : c < 1) : 0 < biasB c := by
  have hlog : Real.log (1-c*c) ≤ 0 := Real.log_nonpos (by nlinarith) (by nlinarith)
  unfold biasB
  linarith [log_two_pos]









end GeneralCK.Reflection
end

section
namespace GeneralCK.Certificates.E8TAxisStableScalar

open GeneralCK.Reflection GeneralCK.Certificates.Reflection
open GeneralCK.E8AnalyticGerm










theorem z_pos (a : ℝ) : 0 < z a := Real.exp_pos _

theorem one_add_z_pos (a : ℝ) : 0 < 1 + z a := by
  linarith [z_pos a]

theorem z_lt_one {a : ℝ} (ha : 0 < a) : z a < 1 := by
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem r_pos {a : ℝ} (ha : 0 < a) : 0 < r a := by
  exact div_pos (sub_pos.mpr (z_lt_one ha)) (one_add_z_pos a)

theorem r_lt_one (a : ℝ) : r a < 1 := by
  change (1 - z a) / (1 + z a) < 1
  apply (div_lt_one (one_add_z_pos a)).mpr
  linarith [z_pos a]

theorem one_add_r (a : ℝ) : 1 + r a = 2 / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_sub_r (a : ℝ) : 1 - r a = 2 * z a / (1 + z a) := by
  unfold r
  field_simp [(one_add_z_pos a).ne'] <;> ring

theorem one_add_r_pos (a : ℝ) : 0 < 1 + r a := by
  rw [one_add_r]
  exact div_pos (by norm_num) (one_add_z_pos a)

theorem one_sub_r_pos (a : ℝ) : 0 < 1 - r a := by
  linarith [r_lt_one a]

theorem q_pos (a : ℝ) : 0 < q a := by
  unfold q
  exact div_pos (mul_pos (by norm_num) (z_pos a)) (pow_pos (one_add_z_pos a) 2)



theorem log_one_add_r (a : ℝ) :
    Real.log (1 + r a) = Real.log 2 - l1 a := by
  rw [one_add_r]
  exact Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (one_add_z_pos a).ne'

theorem log_one_sub_r (a : ℝ) :
    Real.log (1 - r a) = Real.log 2 - 2 * a - l1 a := by
  rw [one_sub_r, Real.log_div (mul_ne_zero (by norm_num) (z_pos a).ne')
      (one_add_z_pos a).ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (z_pos a).ne']
  simp only [z, Real.log_exp, l1]
  ring



theorem biasB_r (a : ℝ) : biasB (r a) = ell a := by
  unfold biasB
  rw [show 1 - r a * r a = (1 + r a) * (1 - r a) by ring,
    Real.log_mul (one_add_r_pos a).ne' (one_sub_r_pos a).ne',
    log_one_add_r, log_one_sub_r]
  unfold ell
  ring



theorem ell_pos {a : ℝ} (ha : 0 < a) : 0 < ell a := by
  rw [← biasB_r]
  exact biasB_pos (r_pos ha) (r_lt_one a)















end GeneralCK.Certificates.E8TAxisStableScalar
end

section
namespace GeneralCK.Certificates.E8TAxisStableJet5

open Set E8TAxisReparamJet5 E8InverseJet5Bridge



noncomputable def zJet : Jet5 := Jet5.expAffine 0 (-2)
noncomputable def onePlusZJet : Jet5 := (Jet5.const 1).add zJet
noncomputable def rJet : Jet5 :=
  ((Jet5.const 1).add zJet.neg).mul onePlusZJet.inv
noncomputable def qJet : Jet5 :=
  ((Jet5.const 4).mul zJet).mul (onePlusZJet.mul onePlusZJet).inv
noncomputable def l1Jet : Jet5 := onePlusZJet.log
noncomputable def ellJet : Jet5 := Jet5.variableJet.add l1Jet
noncomputable def hJet : Jet5 :=
  l1Jet.add ((((Jet5.const 2).mul Jet5.variableJet).mul zJet).mul onePlusZJet.inv)
noncomputable def log2Jet : Jet5 := Jet5.const (Real.log 2)

noncomputable def yJet : Jet5 :=
  ((Jet5.const 2).mul log2Jet.inv).mul
    (Jet5.variableJet.add ((rJet.mul hJet).mul (qJet.mul ellJet).inv))

@[simp] theorem zJet_d0 (a : ℝ) : zJet.d0 a = E8TAxisStableScalar.z a := by
  simp [zJet, Jet5.expAffine, E8TAxisStableScalar.z]

@[simp] theorem onePlusZJet_d0 (a : ℝ) : onePlusZJet.d0 a = 1 + E8TAxisStableScalar.z a := by
  simp [onePlusZJet, Jet5.add, Jet5.const]

@[simp] theorem rJet_d0 (a : ℝ) : rJet.d0 a = E8TAxisStableScalar.r a := by
  simp [rJet, Jet5.mul, Jet5.add, Jet5.neg, Jet5.const, Jet5.inv,
    E8TAxisStableScalar.r, sub_eq_add_neg, div_eq_mul_inv]

@[simp] theorem qJet_d0 (a : ℝ) : qJet.d0 a = E8TAxisStableScalar.q a := by
  simp [qJet, Jet5.mul, Jet5.const, Jet5.inv, E8TAxisStableScalar.q, pow_two, div_eq_mul_inv]

@[simp] theorem l1Jet_d0 (a : ℝ) : l1Jet.d0 a = E8TAxisStableScalar.l1 a := by
  simp [l1Jet, Jet5.log, E8TAxisStableScalar.l1]

@[simp] theorem ellJet_d0 (a : ℝ) : ellJet.d0 a = E8TAxisStableScalar.ell a := by
  simp [ellJet, Jet5.add, Jet5.variableJet, E8TAxisStableScalar.ell]

@[simp] theorem hJet_d0 (a : ℝ) : hJet.d0 a = E8TAxisStableScalar.h a := by
  simp [hJet, Jet5.add, Jet5.mul, Jet5.const, Jet5.variableJet, Jet5.inv,
    E8TAxisStableScalar.h, div_eq_mul_inv]

@[simp] theorem log2Jet_d0 (a : ℝ) : log2Jet.d0 a = Real.log 2 := rfl



@[simp] theorem yJet_d0 (a : ℝ) : yJet.d0 a = E8TAxisStableScalar.Y a := by
  simp [yJet, Jet5.mul, Jet5.add, Jet5.const, Jet5.inv, Jet5.variableJet,
    E8TAxisStableScalar.Y, div_eq_mul_inv]

theorem zJet_soundAt (a : ℝ) : zJet.SoundAt a := Jet5.soundAt_expAffine 0 (-2) a

theorem onePlusZJet_soundAt (a : ℝ) : onePlusZJet.SoundAt a :=
  (Jet5.soundAt_const 1 a).add (zJet_soundAt a)

theorem rJet_soundAt (a : ℝ) : rJet.SoundAt a := by
  unfold rJet
  exact ((Jet5.soundAt_const 1 a).add (zJet_soundAt a).neg).mul
    ((onePlusZJet_soundAt a).inv (by
      rw [onePlusZJet_d0]
      exact (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem qJet_soundAt (a : ℝ) : qJet.SoundAt a := by
  unfold qJet
  exact ((Jet5.soundAt_const 4 a).mul (zJet_soundAt a)).mul
    (((onePlusZJet_soundAt a).mul (onePlusZJet_soundAt a)).inv (by
      change onePlusZJet.d0 a * onePlusZJet.d0 a ≠ 0
      rw [onePlusZJet_d0]
      exact mul_ne_zero (E8TAxisStableScalar.one_add_z_pos a).ne' (E8TAxisStableScalar.one_add_z_pos a).ne'))

theorem l1Jet_soundAt (a : ℝ) : l1Jet.SoundAt a := by
  exact (onePlusZJet_soundAt a).log (by
    rw [onePlusZJet_d0]
    exact (E8TAxisStableScalar.one_add_z_pos a).ne')

theorem ellJet_soundAt (a : ℝ) : ellJet.SoundAt a :=
  (Jet5.soundAt_variable a).add (l1Jet_soundAt a)

theorem hJet_soundAt (a : ℝ) : hJet.SoundAt a := by
  unfold hJet
  exact (l1Jet_soundAt a).add
    ((((Jet5.soundAt_const 2 a).mul (Jet5.soundAt_variable a)).mul
      (zJet_soundAt a)).mul ((onePlusZJet_soundAt a).inv (by
        rw [onePlusZJet_d0]
        exact (E8TAxisStableScalar.one_add_z_pos a).ne')))

theorem log2Jet_soundAt (a : ℝ) : log2Jet.SoundAt a :=
  Jet5.soundAt_const (Real.log 2) a



theorem yJet_soundAt {a : ℝ} (ha : 0 < a) : yJet.SoundAt a := by
  unfold yJet
  exact ((Jet5.soundAt_const 2 a).mul ((log2Jet_soundAt a).inv (by
      rw [log2Jet_d0]
      exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'))).mul
    ((Jet5.soundAt_variable a).add
      (((rJet_soundAt a).mul (hJet_soundAt a)).mul
        (((qJet_soundAt a).mul (ellJet_soundAt a)).inv (by
          change qJet.d0 a * ellJet.d0 a ≠ 0
          rw [qJet_d0, ellJet_d0]
          exact mul_ne_zero (E8TAxisStableScalar.q_pos a).ne' (E8TAxisStableScalar.ell_pos ha).ne'))))













end GeneralCK.Certificates.E8TAxisStableJet5
end

section
namespace GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage

open Set DyadicInterval E8TAxisStableInterval E8TAxisStableScalar







theorem contains_of_between {p : ℕ} {alpha : DyadicInterval p} {a : ℝ}
    (ha : a ∈ Icc (lower alpha) (upper alpha)) : alpha.Contains a := by
  constructor
  · have hh := (div_le_iff₀ (scale_cast_pos p)).mp ha.1
    simpa only [mul_comm] using hh
  · have hh := (le_div_iff₀ (scale_cast_pos p)).mp ha.2
    simpa only [mul_comm] using hh

theorem Y_continuousAt {a : ℝ} (ha : 0 < a) : ContinuousAt Y a := by
  have he : E8TAxisStableJet5.yJet.d0 = Y :=
    funext E8TAxisStableJet5.yJet_d0
  rw [← he]
  exact (E8TAxisStableJet5.yJet_soundAt ha).1.continuousAt

theorem covers_of_endpoint_bounds {p : ℕ} {alpha : DyadicInterval p}
    {sLower sUpper : ℝ}
    (hpos : 0 < alpha.lo) (horder : alpha.lo ≤ alpha.hi)
    (hlo : Y (lower alpha) ≤ sLower) (hhi : sUpper ≤ Y (upper alpha))
    {s : ℝ} (hs : s ∈ Icc sLower sUpper) :
    ∃ a : ℝ, alpha.Contains a ∧ 0 < a ∧ Y a = s := by
  have hloPos : 0 < lower alpha := by
    apply div_pos _ (scale_cast_pos p)
    exact_mod_cast hpos
  have hordered : lower alpha ≤ upper alpha := by
    apply div_le_div_of_nonneg_right _ (scale_cast_pos p).le
    exact_mod_cast horder
  have hcont : ContinuousOn Y (Icc (lower alpha) (upper alpha)) := by
    intro a ha
    exact (Y_continuousAt (hloPos.trans_le ha.1)).continuousWithinAt
  obtain ⟨a, ha, hay⟩ := (intermediate_value_Icc hordered hcont)
    (show s ∈ Icc (Y (lower alpha)) (Y (upper alpha)) from
      ⟨hlo.trans hs.1, hs.2.trans hhi⟩)
  exact ⟨a, contains_of_between ha, hloPos.trans_le ha.1, hay⟩








end GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
end

open GeneralCK GeneralCK.Certificates
open Set GeneralCK.Certificates.DyadicInterval GeneralCK.Certificates.E8TAxisStableInterval
open GeneralCK.Certificates.E8TAxisStableScalar
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
open GeneralCK.Certificates.E8TAxisFirstCellInverseCoverage
theorem solution {p : ℕ} {alpha loBox hiBox : DyadicInterval p}
    {sLower sUpper : ℝ}
    (hpos : 0 < alpha.lo) (horder : alpha.lo ≤ alpha.hi)
    (hl : loBox.Contains (Y (lower alpha)))
    (hu : hiBox.Contains (Y (upper alpha)))
    (hlo : (loBox.hi : ℝ) ≤ (scale p : ℝ) * sLower)
    (hhi : (scale p : ℝ) * sUpper ≤ (hiBox.lo : ℝ))
    {s : ℝ} (hs : s ∈ Icc sLower sUpper) :
    ∃ a : ℝ, alpha.Contains a ∧ 0 < a ∧ Y a = s := by
  apply covers_of_endpoint_bounds hpos horder (s := s) (hs := hs)
  · exact (mul_le_mul_iff_right₀ (scale_cast_pos p)).mp (by simpa [mul_comm] using hl.2.trans hlo)
  · exact (mul_le_mul_iff_right₀ (scale_cast_pos p)).mp (by simpa [mul_comm] using hhi.trans hu.1)
