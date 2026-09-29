-- Prove2me | solution 1 for GeneralCK.Certificates.CorrectionFactorizedProgramKernel.output_value_kdet_of_shapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:56:20.336261+00:00
-- url     : https://prove2.me/submissions/895e86dd-9c2b-4982-aea3-5a58a9c1d929

import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
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
import Mathlib.Topology.Order.MonotoneContinuity

section
namespace GeneralCK.Certificates.BivariateJetProgram










namespace Op













end Op














































theorem value_getD (jets : List BivariateJet2) (i : ℕ) (t : ℝ) :
    (jets.getD i zeroJet).value t=(jets.map (fun j => j.value t)).getD i 0 := by
  induction jets generalizing i with
  | nil => simp [zeroJet,BivariateJet2.const]
  | cons j jets ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i










end GeneralCK.Certificates.BivariateJetProgram
end

section
namespace GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set







































theorem eval_value (shape : Shape) (jets : List BivariateJet2) (t : ℝ) :
    (shape.eval jets).value t=evalReal shape (jets.map (fun j => j.value t)) := by
  cases shape <;> simp only [Shape.eval,evalReal,BivariateJet2.add,BivariateJet2.neg,
    BivariateJet2.mul,BivariateJet2.inv,BivariateJet2.log,BivariateJet2.outerCompose,
    reflectionContactJet,BivariateJetProgram.value_getD]



theorem finalJets_values {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) (t : ℝ) :
    (finalJets program jets).map (fun j => j.value t)=
      evalRealProgram program (jets.map (fun j => j.value t)) := by
  induction program generalizing jets with
  | nil => rfl
  | cons ins rest ih =>
    simpa only [finalJets,evalRealProgram,List.map_cons,eval_value] using
      ih (ins.shape.eval jets::jets)

theorem finalJet_value {p : ℕ} (program : List (Instruction p))
    (jets : List BivariateJet2) (i : ℕ) (t : ℝ) :
    ((finalJets program jets).getD i zeroJet).value t=
      (evalRealProgram program (jets.map (fun j => j.value t))).getD i 0 := by
  rw [BivariateJetProgram.value_getD,finalJets_values]

end GeneralCK.Certificates.BivariateProvedProgram
end

section
namespace GeneralCK.Certificates.CorrectionProgramKernel

open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram









/-- `evalRealProgram` depends only on instruction shapes, not interval
proposals or their precision. -/
theorem evalRealProgram_eq_of_shapes_eq {p q : ℕ}
    {left : List (Instruction p)} {right : List (Instruction q)}
    (h : shapes left = shapes right) (values : List ℝ) :
    evalRealProgram left values = evalRealProgram right values := by
  induction left generalizing right values with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp [shapes] at h
  | cons head tail ih =>
      cases right with
      | nil => simp [shapes] at h
      | cons head' tail' =>
          simp only [shapes, List.map_cons, List.cons.injEq] at h
          rw [evalRealProgram, evalRealProgram, h.1]
          exact ih h.2 _

















end GeneralCK.Certificates.CorrectionProgramKernel
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace GeneralCK.Certificates.CorrectionFactorizedProgramKernel
open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram



private theorem Fs_explicit (c : ℝ) : Correction.Natural.Fs c =
    Real.log ((1+c)/(1-c))+Reflection.biasE c*c/(((1-c^2)/4)*(2*Reflection.biasB c)) := by
  unfold Correction.Natural.Fs SmallMean.A
  ring

theorem scalarCore_eq (a z : ℝ) : scalarCore a z =
    (Correction.Natural.m11 a (a+z*(1/2-a)), Correction.Natural.kdet a (a+z*(1/2-a))) := by
  let w := a+z*(1/2-a)
  have hk : Correction.Natural.kdet a w =
      Correction.Natural.m11 a w *
        (Correction.Natural.nw a w-Correction.Natural.weight a w*Correction.Natural.jn w*(Correction.Natural.zw a w)^2) -
      Correction.Natural.jn w *
        (Correction.Natural.qp a+Correction.Natural.qp w+
          Correction.Natural.weight a w*Correction.Natural.zu a w*Correction.Natural.zw a w)^2 := by
    unfold Correction.Natural.kdet Correction.Natural.m11
    ring
  rw [hk]
  simp only [scalarCore,Correction.Natural.m11,Correction.Natural.au,
    Correction.Natural.nw,Correction.Natural.zu,Correction.Natural.zw,Correction.Natural.weight,
    Fs_explicit,Correction.Natural.Fss,Correction.Natural.contact,Correction.Natural.entropySum,
    Correction.Natural.qp,Correction.Natural.jn,Mixed.hn,Reflection.biasE,Reflection.biasB,
    div_eq_mul_inv,sub_eq_add_neg,pow_succ,pow_zero,one_mul,mul_assoc,neg_mul,w]
  norm_num


theorem scalar_program_kdet (a z : ℝ) :
    (evalRealProgram kernelProgram [a,z,1,2]).getD 0 0 = (scalarCore a z).2 := rfl






end GeneralCK.Certificates.CorrectionFactorizedProgramKernel
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.CorrectionFactorizedProgramKernel
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram
theorem solution {p : ℕ} (program : List (Instruction p))
    (h : shapes program = shapes kernelProgram) (ac zc a z t : ℝ) :
    ((finalJets program (inputJets ac zc a z)).getD 0 zeroJet).value t =
      Correction.Natural.kdet (ac+t*(a-ac)) ((ac+t*(a-ac))+(zc+t*(z-zc))*(1/2-(ac+t*(a-ac)))) := by
  rw [finalJet_value]
  change (evalRealProgram program [ac+t*(a-ac),zc+t*(z-zc),1,2]).getD 0 0 = _
  rw [CorrectionProgramKernel.evalRealProgram_eq_of_shapes_eq h,scalar_program_kdet,scalarCore_eq]
