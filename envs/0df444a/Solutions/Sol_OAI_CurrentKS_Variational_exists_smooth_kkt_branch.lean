-- Prove2me | solution 1 for OAI.CurrentKS.Variational.exists_smooth_kkt_branch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:52:10.142057+00:00
-- url     : https://prove2.me/submissions/38e55b4f-f98f-4697-8027-eac1b23ecfeb

import Mathlib
import Definitions.Def_OAIQ241TT006

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JordanCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r53f378_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
lemma jordanCLM_val (A B U : H d) :
    ((jordanCLM A B U : H d) : Mat d) =
      (A : Mat d) * (U : Mat d) * (B : Mat d) + (B : Mat d) * (U : Mat d) * (A : Mat d) := by
  change ((A : Mat d)+(B : Mat d)) * (U : Mat d) * ((A : Mat d)+(B : Mat d)) -
    (A : Mat d)*(U : Mat d)*(A : Mat d) - (B : Mat d)*(U : Mat d)*(B : Mat d) = _
  noncomm_ring

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
lemma invH_retract (A : H d) : invH A = retractH (Ring.inverse (A : Mat d)) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (retractH_coe (invH A)).symm

lemma contDiffAt_invH {A : H d} (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n invH A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : ContDiffAt ℝ n Ring.inverse (A : Mat d) := by
    rw [← ha]
    exact contDiffAt_ringInverse ℝ a
  have hc := (retractH (d := d)).contDiff.contDiffAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.contDiff.contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun B => invH_retract B

lemma hasFDerivAt_invH {A : H d} (hA : A ∈ pd d) :
    HasFDerivAt invH (-sandwichCLM (invH A)) A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : HasFDerivAt (fun B : Mat d => B⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat d) (A : Mat d)⁻¹ (A : Mat d)⁻¹) (A : Mat d) := by
    rw [← ha]
    simpa only [Matrix.nonsing_inv_eq_ringInverse, Matrix.coe_units_inv] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) a)
  have hc := (retractH (d := d)).hasFDerivAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.hasFDerivAt)
  have he : (fun B : H d => retractH ((B : Mat d)⁻¹)) = invH := by
    funext B
    exact retractH_coe (invH B)
  change HasFDerivAt (fun B : H d => retractH ((B : Mat d)⁻¹)) _ A at hc
  rw [he] at hc
  refine hc.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro U
  change -sandwich (invH A) U = retractH (-((A : Mat d)⁻¹ * (U : Mat d) * (A : Mat d)⁻¹))
  rw [map_neg]
  exact congrArg Neg.neg (retractH_coe (sandwich (invH A) U)).symm

lemma contDiff_sandwich {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : H d × H d => sandwich z.1 z.2) := by
  have hf : (fun z : H d × H d => sandwich z.1 z.2) =
      (fun z : H d × H d => retractH ((z.1 : Mat d) * (z.2 : Mat d) * (z.1 : Mat d))) := by
    funext z
    exact (retractH_coe (sandwich z.1 z.2)).symm
  rw [hf]
  apply (retractH (d := d)).contDiff.comp
  exact (((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst).mul
    ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_snd)).mul
      ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst)

lemma hasFDerivAt_invSandwich (A P : H d) (hA : A ∈ pd d) :
    HasFDerivAt (fun z : H d × H d => sandwich (invH z.1) z.2)
      ((-jordanCLM (invH A) (sandwich (invH A) P)).comp (ContinuousLinearMap.fst ℝ (H d) (H d)) +
       (sandwichCLM (invH A)).comp (ContinuousLinearMap.snd ℝ (H d) (H d))) (A,P) := by
  let val := (hermitianSubmodule d).subtypeL
  have hInv := val.hasFDerivAt.comp (A,P)
    ((hasFDerivAt_invH hA).comp (A,P) (hasFDerivAt_fst (p := (A,P))))
  have hMid := val.hasFDerivAt.comp (A,P) (hasFDerivAt_snd (p := (A,P)))
  have hm := (hInv.mul' hMid).mul' hInv
  have hh := (retractH (d := d)).hasFDerivAt.comp (A,P) hm
  have he : (fun z : H d × H d => retractH
      (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) =
      (fun z : H d × H d => sandwich (invH z.1) z.2) := by
    funext z
    exact retractH_coe (sandwich (invH z.1) z.2)
  change HasFDerivAt (fun z : H d × H d => retractH
    (((invH z.1 : H d) : Mat d) * (z.2 : Mat d) * ((invH z.1 : H d) : Mat d))) _ (A,P) at hh
  rw [he] at hh
  refine hh.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro z
  change -jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2 =
    retractH
      (((invH A : H d) : Mat d) * (P : Mat d) *
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) +
       (((invH A : H d) : Mat d) * (z.2 : Mat d) +
          (-(((invH A : H d) : Mat d) * (z.1 : Mat d) * ((invH A : H d) : Mat d))) * (P : Mat d)) *
        ((invH A : H d) : Mat d))
  rw [← retractH_coe (-jordanCLM (invH A) (sandwich (invH A) P) z.1 + sandwich (invH A) z.2)]
  congr 1
  simp only [Submodule.coe_add, Submodule.coe_neg, jordanCLM_val, sandwich_val]
  noncomm_ring

lemma contDiffAt_invSandwich (A P : H d) (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun z : H d × H d => sandwich (invH z.1) z.2) (A,P) := by
  have hi : ContDiffAt ℝ n (fun z : H d × H d => invH z.1) (A,P) :=
    (contDiffAt_invH (d := d) (A := A) (n := n) hA).fst' (y := P)
  have hp : ContDiffAt ℝ n (fun z : H d × H d => (invH z.1, z.2)) (A,P) :=
    hi.prodMk (contDiffAt_snd (𝕜 := ℝ) (n := n) (p := (A,P)))
  have hs : ContDiffAt ℝ n (fun u : H d × H d => sandwich u.1 u.2) (invH A,P) :=
    (contDiff_sandwich (d := d) (n := n)).contDiffAt
  exact hs.comp (A,P) hp

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma hasFDerivAt_tightPart (t : E →L[ℝ] ℝ) (X Y : E →L[ℝ] H d)
    (S : H d) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => t v • (one : H d) - invH (X v) - S - η (Y v))
      ((t.smulRight (one : H d) : E →L[ℝ] H d) +
        ((sandwichCLM (invH (X z))).comp X : E →L[ℝ] H d) - η.comp Y) z := by
  have h := (((t.hasFDerivAt.smul_const (one : H d)).sub
    ((hasFDerivAt_invH hX).comp z X.hasFDerivAt)).sub_const S).sub
    (η.hasFDerivAt.comp z Y.hasFDerivAt)
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change t v • (one : H d) + sandwich (invH (X z)) (X v) - η (Y v) =
    t v • (one : H d) - (-sandwich (invH (X z)) (X v)) - η (Y v)
  module

lemma hasFDerivAt_stationaryPart (X P Q : E →L[ℝ] H d)
    (ε : ℝ) (η : H d →L[ℝ] H d) (z : E) (hX : X z ∈ pd d) :
    HasFDerivAt (fun v => sandwich (invH (X v)) (P v) - η (Q v) - ε • (one : H d))
      (((sandwichCLM (invH (X z))).comp P : E →L[ℝ] H d) - η.comp Q -
        ((jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z))).comp X : E →L[ℝ] H d)) z := by
  have h := (((hasFDerivAt_invSandwich (X z) (P z) hX).comp z
    (X.hasFDerivAt.prodMk P.hasFDerivAt)).sub
    (η.hasFDerivAt.comp z Q.hasFDerivAt)).sub_const (ε • (one : H d))
  refine h.congr_fderiv ?_
  symm
  apply ContinuousLinearMap.ext
  intro v
  change sandwich (invH (X z)) (P v) - η (Q v) -
      jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) =
    -jordanCLM (invH (X z)) (sandwich (invH (X z)) (P z)) (X v) +
      sandwich (invH (X z)) (P v) - η (Q v)
  module

lemma contDiffAt_tightPart {n : WithTop ℕ∞} {t : E → ℝ} {X Y S : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E}
    (ht : ContDiffAt ℝ n t z) (hX : ContDiffAt ℝ n X z) (hY : ContDiffAt ℝ n Y z)
    (hS : ContDiffAt ℝ n S z) (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z :=
  (((ht.smul contDiffAt_const).sub ((contDiffAt_invH hpos).comp z hX)).sub hS).sub
    (hη.clm_apply hY)

lemma contDiffAt_stationaryPart {n : WithTop ℕ∞} {X P Q : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E} (ε : ℝ)
    (hX : ContDiffAt ℝ n X z) (hP : ContDiffAt ℝ n P z) (hQ : ContDiffAt ℝ n Q z)
    (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z :=
  (((contDiffAt_invSandwich (X z) (P z) hpos).comp z (hX.prodMk hP)).sub
    (hη.clm_apply hQ)).sub contDiffAt_const

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PartialFderiv
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.KKT
noncomputable section
open scoped Topology ContDiff

variable {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma partial_fderiv {F : A × Z → Z} {a : A} {z : Z} {L : Z →L[ℝ] Z}
    (hF : DifferentiableAt ℝ F (a,z))
    (hL : HasFDerivAt (fun v => F (a,v)) L z) :
    (fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z) = L := by
  have hi : HasFDerivAt (fun v : Z => (a,v)) (ContinuousLinearMap.inr ℝ A Z) z := by
    convert (hasFDerivAt_const a z).prodMk (hasFDerivAt_id z) using 1 <;> rfl
  exact (hF.hasFDerivAt.comp z hi).unique hL

lemma smooth_branch [CompleteSpace A] [CompleteSpace Z] {F : A × Z → Z} {a : A} {z : Z}
    (hF : ContDiffAt ℝ ∞ F (a,z)) (J : Z ≃L[ℝ] Z)
    (hJ : HasFDerivAt (fun v => F (a,v)) J.toContinuousLinearMap z) :
    ∃ f : A → Z, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, F (b,f b) = F (a,z) := by
  have hi : ((fderiv ℝ F (a,z)).comp (ContinuousLinearMap.inr ℝ A Z)).IsInvertible := by
    rw [partial_fderiv (hF.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hJ]
    exact ContinuousLinearMap.isInvertible_equiv
  refine ⟨hF.implicitFunction (by simp) hi, hF.implicitFunction_apply_self (by simp) hi,
    hF.contDiffAt_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi, ?_⟩
  exact hF.eventually_apply_implicitFunction (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) hi

end
end CurrentKS.KKT

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Vars
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars
lemma hasFDerivAt_kktSystem (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) :
    HasFDerivAt (kktSystem ε S η)
      (CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) η))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z))) z := by
  have hr := (((innerSL ℝ (identityPair d)).hasFDerivAt.comp z (pCoord d).hasFDerivAt).sub_const 1)
  have hfx := hasFDerivAt_tightPart (tCoord d) (xCoord d) (yCoord d) S η z hX
  have hfy := hasFDerivAt_tightPart (tCoord d) (yCoord d) (xCoord d) (-S) η z hY
  have hfu := (pairEquiv d).symm.hasFDerivAt.comp z (hfx.prodMk hfy)
  have hgx := hasFDerivAt_stationaryPart (xCoord d) (mCoord d) (nCoord d) ε η z hX
  have hgy := hasFDerivAt_stationaryPart (yCoord d) (nCoord d) (mCoord d) ε η z hY
  have hgp := (pairEquiv d).symm.hasFDerivAt.comp z (hgx.prodMk hgy)
  have hf := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hf
  convert hf using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply (pairEquiv d).injective
      apply Prod.ext
      · change sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (xCoord d z)) (xCoord d v) - η (yCoord d v)
        module
      · change sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v) +
          tCoord d v • (Hermitian.one : H d) =
          tCoord d v • (Hermitian.one : H d) + sandwich (invH (yCoord d z)) (yCoord d v) - η (xCoord d v)
        module
    · rfl

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

section

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p4
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdParametersVars
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdParametersVars
lemma contDiffAt_kktGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {v : E → Vars d} {b : E} (ε : ℝ)
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b) (hv : ContDiffAt ℝ n v b)
    (hX : xCoord d (v b) ∈ pd d) (hY : yCoord d (v b) ∈ pd d) :
    ContDiffAt ℝ n (fun a => kktSystem ε (S a) (η a) (v a)) b := by
  have ht := (tCoord d).contDiff.contDiffAt.comp b hv
  have hx := (xCoord d).contDiff.contDiffAt.comp b hv
  have hy := (yCoord d).contDiff.contDiffAt.comp b hv
  have hm := (mCoord d).contDiff.contDiffAt.comp b hv
  have hn := (nCoord d).contDiff.contDiffAt.comp b hv
  have hr := (((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp b
      ((pCoord d).contDiff.contDiffAt.comp b hv)).sub (contDiffAt_const (c := (1 : ℝ))))
  have hfx := contDiffAt_tightPart ht hx hy hS hη hX
  have hfy := contDiffAt_tightPart ht hy hx hS.neg hη hY
  have hfu := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hfx.prodMk hfy)
  have hgx := contDiffAt_stationaryPart ε hx hm hn hη hX
  have hgy := contDiffAt_stationaryPart ε hy hn hm hη hY
  have hgp := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hgx.prodMk hgy)
  have hh := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hh
  exact hh

lemma contDiffAt_kktJoint (ε : ℝ) (a : Parameters d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (kktJoint ε) (a,z) :=
  contDiffAt_kktGiven ε contDiffAt_fst.fst contDiffAt_fst.snd contDiffAt_snd hX hY

theorem exists_smooth_kkt_branch_oai (ε : ℝ) (a : Parameters d) (z : Vars d)
    (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ v, J v = CurrentKS.KKT.jacobian (identityPair d)
        (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) a.2))
        (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) v) :
    ∃ f : Parameters d → Vars d, f a = z ∧ ContDiffAt ℝ ∞ f a ∧
      ∀ᶠ b in 𝓝 a, kktSystem ε b.1 b.2 (f b) = kktSystem ε a.1 a.2 z := by
  have he : CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) a.2))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) = J.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact (hJ v).symm
  have hd := hasFDerivAt_kktSystem ε a.1 a.2 z hX hY
  rw [he] at hd
  exact CurrentKS.KKT.smooth_branch (contDiffAt_kktJoint ε a z hX hY) J hd

end

end CurrentKS.Variational

end

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.Variational.exists_smooth_kkt_branch_oai := @OAI.CurrentKS.Variational.exists_smooth_kkt_branch_oai
